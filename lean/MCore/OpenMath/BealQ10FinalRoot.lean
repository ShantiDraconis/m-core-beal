import MCore.OpenMath.BealQ10FinalMixedLeaf
import MCore.K10

namespace MCore.OpenMath.BealQ10

open MCore.OpenMath.BealProbe

private theorem observedDefect_pos (d : MCore.BealData) :
    0 < observedDefect d := by
  unfold observedDefect
  exact Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ d.a_pos)

private theorem observedDefect_commonDivisor
    (d : MCore.BealData)
    (hgt : 1 < observedDefect d) :
    MCore.CommonDivisor (observedDefect d) d.a d.b d.c := by
  refine ⟨hgt, ?_, ?_, ?_⟩
  · exact MCore.nat_dvd_trans
      (Nat.gcd_dvd_left (Nat.gcd d.a d.b) d.c)
      (Nat.gcd_dvd_left d.a d.b)
  · exact MCore.nat_dvd_trans
      (Nat.gcd_dvd_left (Nat.gcd d.a d.b) d.c)
      (Nat.gcd_dvd_right d.a d.b)
  · exact Nat.gcd_dvd_right (Nat.gcd d.a d.b) d.c

theorem materialPrimitiveExclusion_closes_beal
    (h : MaterialPrimitiveExclusion) :
    MCore.BealConjecture := by
  intro d
  by_contra hcp
  have hNoCommon :
      ¬ ∃ q : Nat, MCore.CommonDivisor q d.a d.b d.c := by
    intro hex
    exact hcp ((MCore.commonPrime_iff_commonDivisor).2 hex)
  have hle : observedDefect d ≤ 1 := by
    by_contra hnot
    have hgt : 1 < observedDefect d := Nat.lt_of_not_ge hnot
    exact hNoCommon ⟨observedDefect d, observedDefect_commonDivisor d hgt⟩
  have hone : 1 ≤ observedDefect d :=
    Nat.succ_le_of_lt (observedDefect_pos d)
  have heq : observedDefect d = 1 := Nat.le_antisymm hle hone
  exact h d heq

/-- Single terminal root. No decomposition below this point is part of certification. -/
def FinalRoot : Prop := FinalMixedExclusion

theorem finalRoot_closes_beal
    (h : FinalRoot) :
    MCore.BealConjecture := by
  exact materialPrimitiveExclusion_closes_beal
    (finalMixedExclusion_closes_Q10 h)

/-- External/global publication root: identical to the frozen terminal root. -/
def GlobalExternalRoot : Prop := FinalRoot

theorem globalExternalRoot_closes_beal
    (h : GlobalExternalRoot) :
    MCore.BealConjecture :=
  finalRoot_closes_beal h

#print axioms MCore.OpenMath.BealQ10.materialPrimitiveExclusion_closes_beal
#print axioms MCore.OpenMath.BealQ10.finalRoot_closes_beal
#print axioms MCore.OpenMath.BealQ10.globalExternalRoot_closes_beal

end MCore.OpenMath.BealQ10
