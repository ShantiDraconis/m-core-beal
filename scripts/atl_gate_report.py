#!/usr/bin/env python3
import json, pathlib, sys
from collections import defaultdict, deque

SEVERITY={"TYPE":0,"BUILD":1,"AXIOM":2,"SEMANTIC":3,"OPEN_MATH":4}

def ancestors(edges):
    parents=defaultdict(set)
    for e in edges:
        parents[e["to"]].add(e["from"])
    memo={}
    def go(x):
        if x in memo: return memo[x]
        seen=set(); stack=list(parents[x])
        while stack:
            y=stack.pop()
            if y in seen: continue
            seen.add(y); stack.extend(parents[y])
        memo[x]=seen; return seen
    return go

def canonical(errors, edges):
    anc=ancestors(edges)
    independent=[]
    ids={e["node"] for e in errors}
    for e in errors:
        # keep errors not downstream of another failing node
        if not (anc(e["node"]) & ids):
            independent.append(e)
    independent.sort(key=lambda e:(SEVERITY.get(e["class"],99),e["node"],e.get("file",""),e.get("line",0)))
    return independent

def main(graph_path, errors_path):
    g=json.loads(pathlib.Path(graph_path).read_text())
    errs=json.loads(pathlib.Path(errors_path).read_text()).get("errors",[])
    indep=canonical(errs,g.get("edges",[]))
    by=defaultdict(list)
    for e in indep: by[e["class"]].append(e)
    out={
      "independent_errors":indep,
      "classes":dict(by),
      "canonical_ties":indep[:1] if len(indep)<2 else [
        e for e in indep if SEVERITY.get(e["class"],99)==SEVERITY.get(indep[0]["class"],99)
      ]
    }
    print(json.dumps(out,indent=2))
if __name__=="__main__":
    main(sys.argv[1],sys.argv[2])
