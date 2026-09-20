# V23 — Behavioral Signature Data Contract

Status: observational/audit contract. This file proves no Beal endpoint.

The mathematical object is behavior. GREEN/RED/FROZEN/CERTIFIED/OPEN_EXACT are audit metadata and are never fields of the behavioral signature itself.

## Per-V raw record

For every mathematical transition Vn -> Vn+1 collect before interpretation:

- STATE: exact typed objects and all arithmetic values/restrictions.
- LOGIC: exact proposition, hypotheses, conclusion, quantifier order, direction.
- POSITION: START / approach / CENTER / departure / END / CROSSING.
- TRANSFORM: input, operation, output, preconditions, postconditions, reversibility.
- BEHAVIOR: monotonicity, stabilization, oscillation, branching, reconvergence, symmetry, saturation, collapse/compression, terminal behavior.
- INVARIANTS: preserved quantities/propositions.
- INFORMATION_PRESERVED and INFORMATION_LOST.
- EXTREMA: min/max/sup/inf, attainment, uniqueness, boundedness.
- CENTER: independently typed middle object/predicate and reachability.
- ZERO_ZERO: typed numerator-like and denominator-like objects, only when both are mathematically defined; path/rate/dependence and resolution transform.
- OMEGA: exact meaning (limit, ordinal/well-founded stage, or structural label), family/sequence, ordering, what tends to zero/diverges/stabilizes.
- COUNTEREXAMPLES: negative controls and near-miss witnesses.
- MINIMAL_HYPOTHESES: remove one assumption at a time and record survival.
- DEPENDENCIES: imported theorem DAG, endpoint leakage/circularity audit.
- PROVENANCE: V, file, theorem/object, SHA, parent SHA, branch, run, job, target, Lean/mathlib revision, #print axioms, artifact/hash when real.

## Detector outputs

Detectors are conclusions, never inputs:

- PATTERN_DETECTED
- INVARIANT_DETECTED
- CENTER_SIGNATURE_DETECTED
- 0_0_SIGNATURE_DETECTED
- OMEGA_BEHAVIOR_DETECTED
- M_CORE_STRUCTURE_DETECTED
- M_CORE_CROSSING_DETECTED
- NOVEL_STRUCTURE_DETECTED
- NO_0_0_SIGNATURE

A 0/0 detector is forbidden unless two concrete typed quantities have been identified and their zero behavior proved/observed under an explicit path.

## Current Beal observations

Canonical residual data preserve a,b,c,x,y,z, positivity, x,y,z >= 3, the exact equation a^x+b^y=c^z, and the exact no-common-prime witness.

V23MiddleSearch.lean currently defines only an experimental middle package: middle predicate, Nat measure, strictly decreasing step, terminality, and the unproved CenterCompressionTarget.

Important defect found by signature audit: MiddleHasIndependentWitness is vacuous as an independence detector because M.middle d -> True contributes no restriction. It must not be used as evidence that state 2 is independent of endpoint states.

No concrete typed pair establishing a 0/0 signature has yet been identified in the canonical Beal modules inspected here.

Therefore:
CENTER MODEL = DEFINED EXPERIMENTALLY
CENTER COMPRESSION = UNPROVED
0/0 SIGNATURE = NOT YET DETECTED
OMEGA UNIVERSALITY = NOT YET DETECTED

## Triple FinalProof comparison

Any future FinalProof must still be independently derived by LEFT, RIGHT/residual, and CENTER routes and compared on endpoint, HC,Q,S,K,A, dependency DAG, information loss, circularity, axioms, and provenance.
