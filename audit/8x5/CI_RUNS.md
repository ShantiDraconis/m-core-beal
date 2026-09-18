# 8x5 CI ledger — Beal

## Run 1 — RED (mechanical)

- source audit commit: `8f577730c351e451041ef5deca63d877356661de`
- workflow: `audit-8x5-beal`
- run: `35376345056`
- job: `105701813818`
- conclusion: `RED_BUILD_GRAPH`

L1-L7 passed. L8 failed because `MCore.Audit8x5` was not imported by the
library root after `lake clean`. This was a build-graph error, not a
mathematical residue.

## Run 2 — GREEN

- source audit commit: `14d553250751522a4ce0605a58941251751a7038`
- workflow: `audit-8x5-beal`
- run: `35376633156`
- job: `105702718253`
- completed: `2026-09-18T17:50:19Z`
- conclusion: `SUCCESS`

All outer locks passed:

- L1 HEAD_EXATO: GREEN
- L2 FROZEN_S1: GREEN
- L3 ENDPOINT_DEFINITION: GREEN
- L4 COMPRESSION: GREEN
- L5 5-axis semantic audit: GREEN
- L6 RESIDUE_CLASSIFIER: GREEN
- L7 K0-K10 + clean MCore build: GREEN
- L8 NO-PLACEBO + exact axiom footprint: GREEN

Exact theorem footprints:

- `beal_iff_deltaStar`: `[propext, Quot.sound]`
- `quantifier_match_iff_deltaStar`: no axioms
- `scaling_match`: no axioms
- `constant_match`: no axioms
- `no_placebo_endpoint`: no axioms

No `sorryAx`, no `Classical.choice`, no project axiom, no source
`sorry/admit`.

Certified signature:

[
Sigma_Beal=(BLOCKING,MATCH,MATCH,MATCH,MATCH).
]

Therefore the K / CONSTANT_MATCH axis is CLOSED. The remaining residue is HC.
No FECHADO-FECHADO-FECHADO certificate is emitted.
