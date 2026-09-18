# 8x5 CI ledger — Beal

## Run 1 — RED (mechanical)

- source audit commit: `8f577730c351e451041ef5deca63d877356661de`
- workflow: `audit-8x5-beal`
- run: `35376345056`
- job: `105701813818`
- conclusion: `RED_BUILD_GRAPH`

Passed before failure:

- L1 HEAD_EXATO: GREEN
- L2 FROZEN_S1 U-REF: GREEN
- L3 ENDPOINT_DEFINITION: GREEN
- L4 semantic source check: source file present; direct Lean call lacked built dependency
- L5 five-axis audit text contract: GREEN
- L6 RESIDUE_CLASSIFIER: GREEN
- L7 K0-K10 build + clean MCore build: GREEN

Failure:

L8 attempted to import `MCore.Audit8x5` after `lake clean && lake build MCore`,
but the root `MCore.lean` did not import `MCore.Audit8x5`. Therefore no
`Audit8x5.olean` existed. The same build-graph issue was visible in L4, where
a pipeline without `pipefail` masked the direct-Lean error.

Classification: `MECHANICAL_RED`, not mathematical residue.

Repair:

- add `import MCore.Audit8x5` to the library root;
- explicitly build `MCore.Audit8x5` before direct compilation;
- run L4 under `set -euo pipefail`;
- rerun the same 8-lock gate without changing Sigma.
