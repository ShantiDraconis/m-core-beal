#!/usr/bin/env python3
import json, pathlib, subprocess, sys

g=json.loads(pathlib.Path("ATL_GRAPH.json").read_text())
nodes=g["nodes"]
ids={n["id"] for n in nodes}
assert len(ids)==len(nodes), "duplicate node id"
for e in g.get("edges",[]):
    assert e["from"] in ids and e["to"] in ids, f"dangling edge {e}"
for n in nodes:
    forbidden={"proof_state","build_state","kernel_state","axiom_state","semantic_state","certificate_state","dependencies","consumers","replacement_route"} & set(n)
    assert not forbidden, f"derived state persisted in {n['id']}: {forbidden}"
    assert n["version"]>=1
    if n.get("superseded_by") is not None:
        assert n["superseded_by"] in ids
print("ATL_GRAPH_CANONICAL=GREEN")
subprocess.run([sys.executable,"scripts/atl_loader.py","ATL_GRAPH.json"],check=True)
subprocess.run([sys.executable,"scripts/atl_cut.py","ATL_GRAPH.json","cost_history.json"],check=True)
json.loads(pathlib.Path("ATL_RETRY_POLICY.json").read_text())
print("ATL_ROUTER=GREEN")
