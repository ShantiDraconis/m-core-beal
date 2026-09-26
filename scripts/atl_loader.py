#!/usr/bin/env python3
import json, pathlib, sys
from collections import defaultdict, deque

DERIVED = {
  "proof_state","build_state","kernel_state","axiom_state","semantic_state",
  "certificate_state","dependencies","consumers","replacement_route"
}

def load_graph(path):
    raw=json.loads(pathlib.Path(path).read_text())
    nodes={n["id"]:n for n in raw["nodes"]}
    edges=raw.get("edges",[])
    deps=defaultdict(list); consumers=defaultdict(list)
    for e in edges:
        deps[e["to"]].append(e["from"])
        consumers[e["from"]].append(e["to"])
    return raw,nodes,deps,consumers

def assert_canonical(nodes):
    for n in nodes.values():
        leaked=DERIVED.intersection(n)
        if leaked:
            raise SystemExit(f"derived-state leak in {n['id']}: {sorted(leaked)}")

def replacement_path(nodes,deps,node_id):
    # derived only: walk explicit edge relation, never a stored string
    seen=set(); out=[]; q=deque([node_id])
    while q:
        x=q.popleft()
        for d in deps.get(x,[]):
            if d not in seen:
                seen.add(d); out.append(d); q.append(d)
    return out

def derive(path):
    raw,nodes,deps,consumers=load_graph(path)
    assert_canonical(nodes)
    result={}
    for i,n in nodes.items():
        result[i]={
          "dependencies":deps.get(i,[]),
          "consumers":consumers.get(i,[]),
          "replacement_route":replacement_path(nodes,deps,i),
          "classification":n.get("classification","UNKNOWN"),
          "proof_state":"DERIVED_AT_READ",
          "certificate_state":"DERIVED_AT_READ"
        }
    return result

if __name__=="__main__":
    p=sys.argv[1] if len(sys.argv)>1 else "ATL_GRAPH.json"
    print(json.dumps(derive(p),indent=2,sort_keys=True))
