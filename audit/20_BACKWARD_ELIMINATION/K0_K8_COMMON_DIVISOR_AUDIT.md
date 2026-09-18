# K0–K8 audit against nontrivial-common-divisor candidate Δ*

STATUS: SOURCE_CATALOG_ONLY / NO_MATHEMATICAL_PROMOTION
TARGET_HEAD: 88ca1d0d692255cfb8d23207e3f84a6cf6768b86
WRITE_BRANCH: audit/multistate-proof-refutation-v1

Candidate obligation:
`∀ d : BealData, ∃ g : Nat, CommonDivisor g d.a d.b d.c`.

This audit asks only whether K0–K8 derive or further decompose that obligation without assuming Beal/equivalent target.

## Historical file pins observed on main

K0 9c4ce585501476744e2c5ffe3b707a10a31743a0
K1 d01b0dad1168a3dbabe35cc120824ad785018532
K2 4b76bd21e3e61ed6f565e58d92039621a51cd884
K3 bdc37d6b0fe47825ffb5036ef0601672bcd1a4e2
K4 c4210b4d456bbf0761cc3120820a50bab46649f0
K5 73710c9b544f0520dedf777cd7c4cf5862ab3ab7
K6 adebcf528c69afa0e165304f6590ff101b8eb1ba
K7 c01a1998618eb0f44a10630635853dedfc0eeaa3
K8 final file commits: c76b1b28808bf5382d74736cbfbaff20c659d995 then ec2fde3e7b4a944ff49d3c5ca0e03de91147d920.

Historical K7 frozen ref 2263d6a... remains immutable and is not rewritten by this audit.

## Literal K0–K8 result at TARGET_HEAD

K0: status/boundary separation only. No Beal arithmetic.
K1: declares commonPrime route openBridge. No arithmetic derivation.
K2: certification node/firewall. No arithmetic derivation.
K3: audit disposition/open gap node. No arithmetic derivation.
K4: no-promotion firewall. No arithmetic derivation.
K5: OpenBridgeFirewall. No arithmetic derivation.
K6: dependency metadata between open nodes. No arithmetic derivation.
K7: binds firewall to literal BealConjecture; certifyBeal requires BealConjecture as input. Circular for deriving the target and therefore cannot discharge Δ*.
K8: exact counterexample/common-prime interfaces. closeBeal_from_commonPrime_witnesses requires `∀ d, CommonPrime ...` as input. It does not derive a common divisor from BealData.

Therefore no K0–K8 theorem derives
`BealData → ∃ g>1, g|a ∧ g|b ∧ g|c`
or provides a strictly weaker arithmetic premise that yields it.

## Compression with K9/K10 already reviewed

K10 proves PrimeDivisorProperty.
K9 proves nontrivial common divisor → common prime using that property.
Thus prime-support/factor propagation is realized and removable wiring.

The first remaining non-circular arithmetic edge in the present corpus is:

`d : BealData ⟶ ∃ g : Nat, CommonDivisor g d.a d.b d.c`.

Expanded:
`a^x+b^y=c^z ∧ a,b,c>0 ∧ x,y,z>2 ⟶ ∃ g, 1<g ∧ g|a ∧ g|b ∧ g|c`.

## 18 controls

T01 PROVENANCE_LOCK REVIEWED.
T02 TYPE_DOMAIN REVIEWED: Nat/BealData/CommonDivisor.
T03 ADMISSIBILITY REVIEWED: exactly fields of BealData.
T04 HYPOTHESIS_MATCH REVIEWED.
T05 CONCLUSION_MATCH REVIEWED.
T06 QUANTIFIER_MATCH REVIEWED: ∀ d then ∃ g.
T07 SCALING_MATCH N/A in current elementary interface.
T08 CONSTANT_MATCH REVIEWED: exponent threshold is 2<x,y,z and divisor threshold 1<g.
T09 AXIOM_AUDIT PARTIAL: existing CI has source-hygiene fail-closed and K9/K10 exact prints; dedicated K0–K8 print log still pending.
T10 NONCIRCULARITY REVIEWED: K7/K8 target-as-input routes excluded.
T11 EXTERNAL_CLASSICAL NOT_USED.
T12 PROOF_SEARCH REVIEWED_IN_CORPUS: no K0–K8 derivation found.
T13 FALSIFICATION_SEARCH OPEN.
T14 EDGE_COMPOSITION REVIEWED: common-divisor output composes through K9/K10 to endpoint.
T15 BACKWARD_NECESSITY REVIEWED for current corpus.
T16 MECHANICAL_BUILD GREEN by current branch CI lineage; dedicated audit-head CI required after this record.
T17 AXIOMS_PRINT PARTIAL: K9/K10 exact footprint known; K0–K8 dedicated footprint pending.
T18 STATE_PROMOTION: candidate remains REVIEWED_NOT_YET_BLOCKING until T09/T13/T17 policy is completed.

## Current state

PRIME_SUPPORT = REALIZED / NOT_BLOCKING.
K0_K8_DECOMPOSITION = EXHAUSTED_IN_CURRENT_CORPUS.
CANDIDATE_DELTA_STAR = BEALDATA_TO_NONTRIVIAL_COMMON_DIVISOR.
CANDIDATE_STATUS = REVIEWED_NOT_YET_BLOCKING.
