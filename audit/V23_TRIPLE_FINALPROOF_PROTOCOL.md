# V23 — Triple derivation protocol for any future Beal FinalProof

This protocol does not assert BealConjecture and does not admit the proposed
center-compression theorem. It specifies how a future candidate FinalProof
must be independently derived and compared before promotion.

## Canonical endpoint

Final := BealConjecture

Current open center:
CenterCompressionTarget / omega-closure remains OPEN_EXACT.

## Derivation A — counterexample/minimal-descent route

1. Assume the exact negated endpoint: NoCommonPrimeCandidate.
2. Extract an admissible counterexample candidate.
3. Establish a well-founded minimal counterexample under a precisely defined
   Nat-valued size.
4. Derive the independently proved middle-state conditions.
5. Apply a proved center-compression/descent theorem.
6. Obtain either a strictly smaller counterexample (contradicting minimality)
   or CommonPrime for the same relevant datum.
7. Discharge the negated endpoint and conclude BealConjecture.

No step may use BealConjecture, PrimitiveObstruction, or an equivalent result
as a hidden premise.

## Derivation B — normalized-residual route

1. Use the certified equivalences:
   NoCommonPrimeCandidate ↔ Nonempty PrimitiveBealCandidate
   ↔ Nonempty NormalizedBealCandidate.
2. Derive arithmetic invariants of every normalized candidate.
3. Prove those invariants make the terminal normalized residual impossible.
4. Conclude PrimitiveObstruction.
5. Use primitiveObstruction_iff_beal to conclude BealConjecture.

This derivation must not import the proof term produced by Derivation A.

## Derivation C — endpoint/compression route

1. Define the middle predicate and compression dynamics independently of the
   endpoint truth value.
2. Prove reachability/coverage for every candidate relevant to the negated
   endpoint.
3. Prove well-foundedness/strict decrease of the compression relation.
4. Prove the terminal theorem:
   MiddleTerminal d → CommonPrime d.a d.b d.c.
5. Compose coverage + termination + terminal theorem to eliminate every
   NoCommonPrimeCandidate.
6. Conclude BealConjecture through the canonical endpoint theorem.

This derivation must not import proof terms from A or B.

## Mandatory three-way comparison

Before FinalProof promotion, compare A/B/C on:
- exact endpoint statement;
- hypotheses and conclusions;
- quantifier order and domains;
- scaling/normalization assumptions;
- constants and bounds;
- axiom footprint (#print axioms);
- imported theorem dependency DAG;
- counterexample behavior;
- directionality of every equivalence/implication;
- information lost/preserved at each reduction;
- circularity / endpoint leakage;
- proof SHA, run, job, target and artifact hash.

Required result:
ENDPOINT_MATCH = true for A/B/C.
HC,Q,S,K,A signatures must all match the canonical endpoint requirements.
No derivation may merely wrap or import another derivation's final proof term.

## Promotion rule

FINAL_TRIPLE_DERIVATION = GREEN only if:
- A compiles independently;
- B compiles independently;
- C compiles independently;
- all three prove the exact same canonical BealConjecture;
- dependency audit establishes the required independence;
- semantic signatures agree;
- no sorry/admit/new axiom/placebo is present.

Until then:
FINAL_TRIPLE_DERIVATION = OPEN_EXACT
FINALPROOF = NOT_PROMOTED
