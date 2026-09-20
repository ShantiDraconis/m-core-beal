import MCore.K10

namespace MCore

/-- V0 residue: starting from the actual Beal data (including the
    Diophantine equation and exponents > 2), produce a nontrivial
    common divisor of a, b, and c. -/
def V0EquationToCommonDivisor : Prop :=
  ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c

/-- T0: any Beal proof implies the V0 divisor residue. -/
theorem T0_beal_to_v0
    (h : BealConjecture) : V0EquationToCommonDivisor := by
  intro d
  exact (commonPrime_iff_commonDivisor).mp (h d)

/-- T1 / V1 backward closure: once V0 is discharged, K10 converts the
    nontrivial common divisor into a common prime, closing Beal. -/
theorem T1_v0_to_beal
    (h : V0EquationToCommonDivisor) : BealConjecture := by
  intro d
  exact (commonPrime_iff_commonDivisor).mpr (h d)

/-- V2 collision: after K10, the Beal endpoint is exactly equivalent to V0.
    This isolates the remaining mathematical bridge without promoting it. -/
theorem T2_v2_collision :
    BealConjecture ↔ V0EquationToCommonDivisor :=
  ⟨T0_beal_to_v0, T1_v0_to_beal⟩

#print axioms MCore.T0_beal_to_v0
#print axioms MCore.T1_v0_to_beal
#print axioms MCore.T2_v2_collision

end MCore
