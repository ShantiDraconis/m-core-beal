# Beal certification architecture — 8 ⊃ 5

WRITE_BRANCH: `audit/multistate-proof-refutation-v1`

Frozen input HEAD:

`5b5aa8e0ea0aef519d236422459975918d38a968`

The old K0–K8 audit remains immutable evidence. This layer reclassifies it
under the universal 8-lock container and 5-axis semantic signature.

## Eight external locks

| Lock | Meaning | Beal test |
|---|---|---|
| L1 | HEAD_EXATO | exact 40-char runtime SHA + frozen source SHA |
| L2 | FROZEN_S1 | U-REF repo/SHA/path/theorem verified from Git object |
| L3 | ENDPOINT_DEFINITION | literal `BealConjecture` |
| L4 | COMPRESSION | `BealConjecture ↔ DeltaStar` |
| L5 | 6D_AUDIT | internal Sigma5 = HC,Q,S,K,A; H+C compressed into HC |
| L6 | RESIDUE_CLASSIFIER | RAW→REVIEWED→{CERTIFIED,BLOCKING,REFUTED,EXTERNAL} |
| L7 | BUILD | K0..K10 + clean MCore build |
| L8 | NO-PLACEBO | source hygiene + K7 negative certificate + axiom audit |

## Frozen S1 U-REF

`ShantiDraconis/m-core-beal@5b5aa8e0ea0aef519d236422459975918d38a968/lean/MCore/K10.lean::commonPrime_iff_commonDivisor`

This is read-only evidence. The audit branch is the only writer.

## Five-axis signature

Before the new CI:

[
Sigma_{Beal}=(HC,Q,S,K,A)
=(BLOCKING,MATCH,MATCH,MATCH,PENDING).
]

Evidence already formalized:

- **Q=MATCH**: exact `∀ d : BealData, ∃ g` order.
- **S=MATCH**: K9/K10 transform no Beal datum or exponent.
- **K=MATCH**: exponents remain strictly (>2); nontrivial divisor remains (>1).
- **HC=BLOCKING**: `DeltaStar` is Lean-proved equivalent to `BealConjecture`.
  K0–K8 do not derive DeltaStar, so the remaining arithmetic edge is not a
  weaker already-closed lemma.
- **A=PENDING** until the exact source/axiom/no-placebo CI succeeds.

Thus the old question “is K=0 blocking?” is answered by the new semantics:
the **constant axis K is not the blocker** if this CI passes. The unresolved
nature is HC.

No FECHADO-FECHADO-FECHADO emission is allowed until all eight locks are
GREEN and all five axes are MATCH.
