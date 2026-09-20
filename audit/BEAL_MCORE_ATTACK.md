# Beal × M-Core attack architecture

Scientific endpoint: `MCore.BealConjecture`.

Certified reductions must never be confused with a proof of the conjecture.

## Primary chain

`BealConjecture`
→ `PrimitiveObstruction`
→ no `NormalizedBealCandidate`
→ no `PrimitiveBealCandidate`
→ no `NoCommonPrimeCandidate`.

The equivalences are exact. The unresolved mathematical content is
`PrimitiveObstruction`.

## Parallel attack lanes

1. START→CENTER: derive arithmetic consequences from a normalized candidate.
2. END→CENTER: identify a sufficient contradiction theorem and decompose its hypotheses.
3. COUNTEREXAMPLE: finite searches are falsification tools only; absence of a hit is never proof.
4. ARBITER: every child is PROVED, REFUTED, BLOCKING, or OPEN_EXACT.

## Next mathematical decomposition

Do not encode the desired conclusion as a hypothesis. The next child must establish a genuinely stronger arithmetic property of every `NormalizedBealCandidate` (for example a proved coprimality/valuation/congruence consequence) and show how that property reduces the parent obstruction.

No `sorry`, `admit`, new axioms, or theorem whose assumption is equivalent to its conclusion.
