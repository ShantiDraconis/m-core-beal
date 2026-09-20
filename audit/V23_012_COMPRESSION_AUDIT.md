# V23 — 0/1/2 compression hypothesis audit

This file records the proposed three-state model before it is admitted into the Beal proof chain.

## Proposed labels

- 0: counterexample side / no common prime.
- 1: common-prime side.
- 2: proposed middle state (`IsMaximalMiddle` / "point care").

## Repository evidence audit

At V22, the canonical formal objects are:
- `CommonPrime`;
- `BealCounterexample d := ¬ CommonPrime ...`;
- `NoCommonPrimeCandidate`;
- `PrimitiveBealCandidate`;
- `NormalizedBealCandidate`;
- `PrimitiveObstruction`.

The following proposed objects are NOT YET canonical Lean theorems/definitions in the Beal chain:
- `IsMaximalMiddle`;
- `eval_final`;
- `compress_center`;
- `quebra_central_forca_verdadeiro`;
- the omega/maximize-b compression mechanism.

Therefore no theorem `2 → 1` is certified here.

## Semantic warning

For a fixed admissible datum d, `CommonPrime d.a d.b d.c` and `BealCounterexample d` are logical complements by definition. This gives a 0/1 classification once the proposition is decided; it does not construct an independent mathematical state 2.

A genuine state 2 must be defined by additional arithmetic structure and shown to be neither a renaming of 1 nor a renaming of 0.

## Required V23 construction

To promote the three-state compression model, prove all of:
1. a precise Lean definition of the middle state;
2. existence/reachability conditions for that state;
3. a well-defined compression/descent relation;
4. strict progress or a well-founded measure;
5. the theorem that compression of every relevant middle state reaches the common-prime side, or else an explicitly classified residual;
6. hypothesis, conclusion, quantifier, scaling, constant, and axiom audits;
7. no circular dependency on `BealConjecture` or `PrimitiveObstruction`.

Until then:
THREE_STATE_MODEL = HYPOTHESIS
CENTER_COMPRESSION = OPEN_EXACT
CROSSING_STATUS = NOT_DETECTED
