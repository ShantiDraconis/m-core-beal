# G3 — Literal Oracle / Without-Oracle Collision

STATUS: SOURCE_CATALOG_ONLY / NO_MATHEMATICAL_PROMOTION
TARGET_HEAD: 88ca1d0d692255cfb8d23207e3f84a6cf6768b86
WRITE_BRANCH: audit/multistate-proof-refutation-v1
K7_FROZEN: 2263d6a... (immutable historical checkpoint)

## Literal inputs at TARGET_HEAD

### HypotheticalClosureOracle.lean
`HypotheticalClosure : Prop := BealConjecture`.

`hypothetical_common_prime (H : HypotheticalClosure) (d : BealData) : CommonPrime d.a d.b d.c := H d`.

The oracle therefore supplies the final proposition itself. This route is CLOSED_MODEL only and is rejected as an independent proof path by NONCIRCULARITY.

### WithoutOracle.lean
`CommonPrimeWitnessContract.witness : ∀ d : BealData, CommonPrime d.a d.b d.c`.

`witness_contract_closes_beal (W : CommonPrimeWitnessContract) : BealConjecture := W.witness`.

`bealWithoutOracleClosed : Bool := false` with theorem proving that marker equals false.

## Literal endpoint

From BealSpecification.lean:

`BealData` contains positive a,b,c; exponents x,y,z > 2; and equation `a^x + b^y = c^z`.

`CommonPrime a b c := ∃ p, IsPrime p ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c`.

`BealConjecture := ∀ d : BealData, CommonPrime d.a d.b d.c`.

## Candidate first delta

DELTA_OBJECT: common-prime witness
DELTA_OPERATOR: construct p from arbitrary d : BealData
DELTA_HYPOTHESIS: BealData only
DELTA_CONCLUSION: ∃ p, IsPrime p ∧ p∣a ∧ p∣b ∧ p∣c
DELTA_QUANTIFIER: ∀ d, ∃ p
DELTA_SCALING: N/A at this literal interface; no scaling parameter occurs
DELTA_CONSTANT: exponent threshold is encoded as 2 < x,y,z; no extra uniform constant occurs
DELTA_AXIOM: oracle route imports the target as hypothesis; independent route does not derive witness

CANDIDATE_DELTA_STAR:
`∀ d : BealData, ∃ p : Nat, IsPrime p ∧ p ∣ d.a ∧ p ∣ d.b ∧ p ∣ d.c`.

This is not promoted to BLOCKING until all controls below are reviewed.

## 18-control review

T01 PROVENANCE_LOCK: REVIEWED — target HEAD and literal paths recorded.
T02 TYPE_DOMAIN: REVIEWED — Nat-valued BealData and CommonPrime.
T03 ADMISSIBILITY: REVIEWED — positivity, exponent >2, equation are fields of BealData.
T04 HYPOTHESIS_MATCH: REVIEWED — oracle assumes HypotheticalClosure = BealConjecture; without-oracle accepts witness contract.
T05 CONCLUSION_MATCH: REVIEWED — both routes terminate in CommonPrime/BealConjecture.
T06 QUANTIFIER_MATCH: REVIEWED — endpoint is ∀ BealData then existential common prime.
T07 SCALING_MATCH: REVIEWED/N-A — no scaling variable in literal interface.
T08 CONSTANT_MATCH: REVIEWED — threshold is literal 2<x,y,z.
T09 AXIOM_AUDIT: REVIEW_PENDING_CI — #print axioms statements are present in both source files; log still required for this target HEAD.
T10 NONCIRCULARITY: REFUTED_PATH — HypotheticalClosure is definitionally BealConjecture, so oracle route cannot certify Beal independently.
T11 EXTERNAL_CLASSICAL: NOT_USED at this collision.
T12 PROOF_SEARCH: OPEN — independent construction of common-prime witness not present in compared files.
T13 FALSIFICATION_SEARCH: OPEN — no independent exact counterexample result established by compared files.
T14 EDGE_COMPOSITION: REVIEWED — witness contract closes endpoint mechanically.
T15 BACKWARD_NECESSITY: REVIEWED — witness is exactly the endpoint payload under current specification; further decomposition is required to find a strictly weaker non-circular frontier.
T16 MECHANICAL_BUILD: REVIEW_PENDING_CI.
T17 AXIOMS_PRINT: REVIEW_PENDING_CI.
T18 STATE_PROMOTION: REVIEWED — no mathematical promotion.

## State

ORACLE_ALIAS_FINAL = REFUTED as independent proof path.
WITHOUT_ORACLE_INTERFACE = CERTIFIED_SPECIFICATION only.
CANDIDATE_DELTA_STAR = REVIEWED, NOT_YET_BLOCKING.
BEAL_PROVED = false / no claim.
NEXT_DENSE_ACTION = decompose CommonPrimeWitness into strictly weaker arithmetic obligations and rerun T01–T18 until the first non-circular non-derived edge is isolated.
