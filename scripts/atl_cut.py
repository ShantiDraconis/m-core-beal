#!/usr/bin/env python3
import json, pathlib, sys, math
from collections import defaultdict

ATTACKABLE={"OPEN_MATH_ATTACKABLE"}

def score(node, hist, downstream):
    h=hist.get(node["kind"],{})
    cycles=float(h.get("mean_cycles",5.0))
    fail=float(h.get("failure_probability",0.5))
    cost=max(cycles*max(fail,0.05),0.05)
    unlock=max(float(downstream.get(node["id"],1.0)),1.0)
    return cost/unlock

def main(graph_path="ATL_GRAPH.json", history_path="cost_history.json"):
    g=json.loads(pathlib.Path(graph_path).read_text())
    hist=json.loads(pathlib.Path(history_path).read_text()) if pathlib.Path(history_path).exists() else {}
    downstream=g.get("downstream_unlock",{})
    candidates=[n for n in g["nodes"] if n.get("classification") in ATTACKABLE]
    ranked=sorted(((score(n,hist,downstream),n["id"]) for n in candidates))
    print(json.dumps({"metric":"cost/downstream_unlock","ranked":[{"id":i,"cut_value":s} for s,i in ranked]},indent=2))
if __name__=="__main__":
    main(*(sys.argv[1:3]))
