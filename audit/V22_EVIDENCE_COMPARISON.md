# V22 evidence comparison — Beal

## Evidence collected

### Endpoint
`BealConjecture := ∀ d : BealData, CommonPrime d.a d.b d.c`.

### Exact negation
`NoCommonPrimeCandidate := ∃ d : BealData, BealCounterexample d` and
`NoCommonPrimeCandidate ↔ ¬ BealConjecture`.

### V22 residual wiring
`NoCommonPrimeCandidate ↔ Nonempty PrimitiveBealCandidate`.
`Nonempty PrimitiveBealCandidate ↔ Nonempty NormalizedBealCandidate`.
`PrimitiveObstruction := ¬ Nonempty NormalizedBealCandidate`.
`PrimitiveObstruction ↔ BealConjecture`.

### Arithmetic evidence already closed
Every BealData carries positivity, exponents > 2 (hence >= 3), and the exact exponential equation.
A common prime implies a nontrivial common divisor.
K10 additionally proves the converse common-divisor/common-prime equivalence through the local prime-divisor property.

## Comparison of the two attack directions

START side currently preserves:
- admissible BealData;
- positivity;
- exponent bounds;
- exact equation;
- exact no-common-prime condition for a counterexample candidate.

END side currently requires:
- impossibility of any NormalizedBealCandidate.

The present meeting object is syntactic/logical only: `NormalizedBealCandidate`.
There is not yet an independently derived arithmetic CROSSING_NODE. Therefore:
CROSSING_STATUS = NOT_YET_DETECTED.

## M-Core structure

M_CORE_STRUCTURE_DETECTED = YES.
Pattern: endpoint ↔ exact obstruction ↔ normalized residual.
This is a structural instantiation only; it does not close the mathematical residual.

## Information audit

INFORMATION_PRESERVED:
- all six variables A,B,C,x,y,z;
- positivity;
- exponent lower bounds;
- exact equation;
- no-common-prime predicate.

INFORMATION_LOST:
- none in primitive ↔ normalized packaging proved so far.

NEW_ARITHMETIC_INFORMATION:
- none in V22 beyond consequences already stored in BealData.

## Exact frontier

OPEN_EXACT = PrimitiveObstruction.

The next V must derive a nontrivial arithmetic invariant from every NormalizedBealCandidate. It must not restate PrimitiveObstruction or assume an equivalent of BealConjecture.

Candidate families to investigate, each requiring proof before admission:
- pairwise gcd/coprimality consequences;
- prime valuations;
- parity/congruence restrictions;
- exponent reductions;
- minimal-counterexample descent.

A computational search can falsify a proposed invariant but cannot certify Beal from absence of counterexamples.
