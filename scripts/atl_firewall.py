#!/usr/bin/env python3
import json, pathlib, sys

def check_axiom(n):
    bad=set(n.get("axioms",[]))-set(n.get("axiom_base",[]))
    return not bad, sorted(bad)
def check_circular(n):
    return not bool(n.get("circular",False)), n.get("cycle",[])
def check_semantic(n):
    return n.get("statement_hash")==n.get("frozen_statement_hash"), {
      "actual":n.get("statement_hash"),"expected":n.get("frozen_statement_hash")}
def check_interface(n):
    return not bool(n.get("prop_as_computable_data",False)), n.get("interface_note","")
def check_vacuous(n):
    return not bool(n.get("vacuous",False)), n.get("vacuous_reason","")

CHECKS=[
 ("AXIOM",check_axiom),("CIRCULARITY",check_circular),("SEMANTIC",check_semantic),
 ("INTERFACE",check_interface),("VACUOUS",check_vacuous)
]

def run(path):
    n=json.loads(pathlib.Path(path).read_text())
    rs=[]; ok=True
    for name,fn in CHECKS:
        passed,detail=fn(n); ok &= passed
        rs.append({"firewall":name,"passed":passed,"detail":detail})
    return {"passed":ok,"results":rs}
if __name__=="__main__":
    print(json.dumps(run(sys.argv[1]),indent=2))
