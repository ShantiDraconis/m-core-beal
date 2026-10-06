import MCore.OpenMath.BealQ10SixFamilyMinCut
import Theorems.Thm_fermat_last_theorem

namespace MCore.OpenMath.BealQ10

/-- Full FLT, imported from the pinned complete Lean formalization, kills the equal-odd-prime family. -/
theorem equalOddPrime_eliminated_external : EqualOddPrimeEliminated := by
  intro r hEq
  rcases hEq with ⟨p, hp, hx, hy, hz⟩
  have hp3 : 3 ≤ p := by omega
  have hne :=
    fermat_last_theorem p hp3 r.a r.b r.c r.a_pos r.b_pos r.c_pos
  apply hne
  simpa [hx, hy, hz] using r.equation

/-- Exact residual min-cut after FLT4 and full FLT eliminate the equal-exponent families. -/
structure FiveMixedFamilyMinCut : Prop where
  twoFourPrime : TwoFourPrimeEliminated
  oneFourEqualPrimes : OneFourEqualPrimesEliminated
  oneFourDistinctPrimes : OneFourDistinctPrimesEliminated
  twoEqualOddPrimes : TwoEqualOddPrimesEliminated
  threeDistinctOddPrimes : ThreeDistinctOddPrimesEliminated

def FiveMixedFamilyMinCut.toSix (K : FiveMixedFamilyMinCut) : SixFamilyMinCut where
  equalOddPrime := equalOddPrime_eliminated_external
  twoFourPrime := K.twoFourPrime
  oneFourEqualPrimes := K.oneFourEqualPrimes
  oneFourDistinctPrimes := K.oneFourDistinctPrimes
  twoEqualOddPrimes := K.twoEqualOddPrimes
  threeDistinctOddPrimes := K.threeDistinctOddPrimes

theorem fiveMixedFamilyMinCut_closes_Q10
    (K : FiveMixedFamilyMinCut) :
    MCore.OpenMath.BealProbe.MaterialPrimitiveExclusion :=
  sixFamilyMinCut_closes_Q10 K.toSix

#print axioms MCore.OpenMath.BealQ10.equalOddPrime_eliminated_external
#print axioms MCore.OpenMath.BealQ10.fiveMixedFamilyMinCut_closes_Q10

end MCore.OpenMath.BealQ10
