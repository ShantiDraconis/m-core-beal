import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem neven_iff_mod2_one (n : Nat) :
    (¬ Even n) ↔ n % 2 = 1 := by
  unfold Even
  constructor
  · intro h
    have hpos : 0 < n % 2 := Nat.emod_pos_of_not_dvd h
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  · intro hm hd
    have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega

private theorem odd_res16
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨
    n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by
  have hpar : (n % 16) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 16)).trans hn
  have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
  omega

private theorem odd_fourth16
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 16 = 1 := by
  rcases odd_res16 hn with h | h | h | h | h | h | h | h
  all_goals simp [Nat.pow_mod, h]

private theorem even_fourth16
    {n : Nat}
    (hn : Even n) :
    n ^ 4 % 16 = 0 := by
  rcases hn with ⟨k, rfl⟩
  simp [mul_pow, Nat.mul_mod]

private def reducedData (r : ReducedPrimitiveCandidate) : BealData where
  a := r.a
  b := r.b
  c := r.c
  x := r.x
  y := r.y
  z := r.z
  a_pos := r.a_pos
  b_pos := r.b_pos
  c_pos := r.c_pos
  x_gt_two := r.x_reduced.1
  y_gt_two := r.y_reduced.1
  z_gt_two := r.z_reduced.1
  equation := r.equation

private theorem reducedExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c := by
  have hpw : PairwisePrimitive r.a r.b r.c := by
    constructor
    · intro h
      exact r.no_common (ab_pair_forces_common (reducedData r) h)
    · constructor
      · intro h
        exact r.no_common (ac_pair_forces_common (reducedData r) h)
      · intro h
        exact r.no_common (bc_pair_forces_common (reducedData r) h)
  exact exactlyOneEven_of_pairwise (reducedData r) hpw

/-- Core-only residue atlas for the x=z=4 orientation. -/
theorem twoFour_xz_residue_atlas
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4) :
    (Even r.a → r.b ^ r.y % 16 = 1) ∧
    (Even r.b → r.a ^ 4 % 16 = 1) ∧
    (Even r.c → r.b ^ r.y % 16 = 15) := by
  have hE := reducedExactlyOneEven r
  constructor
  · intro ha
    have hcOdd : r.c % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact (neven_iff_mod2_one r.c).mp hA.2.2
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    have hA16 : r.a ^ 4 % 16 = 0 := even_fourth16 ha
    have hC16 : r.c ^ 4 % 16 = 1 := odd_fourth16 hcOdd
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    rw [hx, hz, Nat.add_mod, hA16, hC16] at hmod
    omega
  constructor
  · intro hb
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (neven_iff_mod2_one r.a).mp hB.1
      · exact False.elim (hC.2.1 hb)
    exact odd_fourth16 haOdd
  · intro hc
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (neven_iff_mod2_one r.a).mp hC.1
    have hA16 : r.a ^ 4 % 16 = 1 := odd_fourth16 haOdd
    have hC16 : r.c ^ 4 % 16 = 0 := even_fourth16 hc
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    rw [hx, hz, Nat.add_mod, hA16, hC16] at hmod
    omega

/-- Core-only residue atlas for the y=z=4 orientation. -/
theorem twoFour_yz_residue_atlas
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4) :
    (Even r.a → r.b ^ 4 % 16 = 1) ∧
    (Even r.b → r.a ^ r.x % 16 = 1) ∧
    (Even r.c → r.a ^ r.x % 16 = 15) := by
  have hE := reducedExactlyOneEven r
  constructor
  · intro ha
    have hbOdd : r.b % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact (neven_iff_mod2_one r.b).mp hA.2.1
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    exact odd_fourth16 hbOdd
  constructor
  · intro hb
    have hcOdd : r.c % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (neven_iff_mod2_one r.c).mp hB.2.2
      · exact False.elim (hC.2.1 hb)
    have hB16 : r.b ^ 4 % 16 = 0 := even_fourth16 hb
    have hC16 : r.c ^ 4 % 16 = 1 := odd_fourth16 hcOdd
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    rw [hy, hz, Nat.add_mod, hB16, hC16] at hmod
    omega
  · intro hc
    have hbOdd : r.b % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (neven_iff_mod2_one r.b).mp hC.2.1
    have hB16 : r.b ^ 4 % 16 = 1 := odd_fourth16 hbOdd
    have hC16 : r.c ^ 4 % 16 = 0 := even_fourth16 hc
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    rw [hy, hz, Nat.add_mod, hB16, hC16] at hmod
    omega

private theorem odd_fourth8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  rcases odd_res16 hn with h | h | h | h | h | h | h | h
  all_goals simp [Nat.pow_mod, h]

private theorem even_pow8_gt_two
    {n e : Nat}
    (hn : Even n)
    (he : 2 < e) :
    n ^ e % 8 = 0 := by
  rcases hn with ⟨k, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : Nat, e = m + 3 := by
    refine ⟨e - 3, ?_⟩
    omega
  subst e
  simp [pow_add, mul_pow, Nat.mul_mod]

/-- The x=y=4 orientation cannot place the even base on the right. -/
theorem twoFour_xy_rhs_not_even_atlas
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    ¬ Even r.c := by
  intro hc
  have hE := reducedExactlyOneEven r
  have haOdd : r.a % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact (neven_iff_mod2_one r.a).mp hB.1
    · exact (neven_iff_mod2_one r.a).mp hC.1
  have hbOdd : r.b % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact (neven_iff_mod2_one r.b).mp hA.2.1
    · exact False.elim (hB.2.2 hc)
    · exact (neven_iff_mod2_one r.b).mp hC.2.1
  have hA8 : r.a ^ 4 % 8 = 1 := odd_fourth8 haOdd
  have hB8 : r.b ^ 4 % 8 = 1 := odd_fourth8 hbOdd
  have hC8 : r.c ^ r.z % 8 = 0 := even_pow8_gt_two hc r.z_reduced.1
  have hmod := congrArg (fun n : Nat => n % 8) r.equation
  rw [hx, hy, Nat.add_mod, hA8, hB8, hC8] at hmod
  omega

/-- The x=y=4 orientation forces the RHS power to 1 mod 16. -/
theorem twoFour_xy_rhs_pow_mod16_atlas
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    r.c ^ r.z % 16 = 1 := by
  have hE := reducedExactlyOneEven r
  have hcOdd := twoFour_xy_rhs_not_even_atlas r hx hy
  rcases hE with hA | hB | hC
  ·
    have hbOdd : r.b % 2 = 1 := (neven_iff_mod2_one r.b).mp hA.2.1
    have hA16 : r.a ^ 4 % 16 = 0 := even_fourth16 hA.1
    have hB16 : r.b ^ 4 % 16 = 1 := odd_fourth16 hbOdd
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
  ·
    have haOdd : r.a % 2 = 1 := (neven_iff_mod2_one r.a).mp hB.1
    have hA16 : r.a ^ 4 % 16 = 1 := odd_fourth16 haOdd
    have hB16 : r.b ^ 4 % 16 = 0 := even_fourth16 hB.2.1
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
  · exact False.elim (hcOdd hC.2.2)

/-- Concrete residue payload for a two-four-prime candidate. -/
def TwoFourResiduePressure (r : ReducedPrimitiveCandidate) : Prop :=
  (r.x = 4 ∧ r.y = 4 ∧ OddPrimeExponent r.z ∧
      r.c ^ r.z % 16 = 1) ∨
  (r.x = 4 ∧ r.z = 4 ∧ OddPrimeExponent r.y ∧
      ((Even r.a → r.b ^ r.y % 16 = 1) ∧
       (Even r.b → r.a ^ 4 % 16 = 1) ∧
       (Even r.c → r.b ^ r.y % 16 = 15))) ∨
  (r.y = 4 ∧ r.z = 4 ∧ OddPrimeExponent r.x ∧
      ((Even r.a → r.b ^ 4 % 16 = 1) ∧
       (Even r.b → r.a ^ r.x % 16 = 1) ∧
       (Even r.c → r.a ^ r.x % 16 = 15)))

/--
Every (4,4,p) reduced candidate is forced into an explicit mod-16 pressure
payload.  This is a strict strengthening of the raw signature classification.
-/
theorem twoFourPrime_forces_residue_pressure
    (r : ReducedPrimitiveCandidate)
    (h : TwoFourPrime r.x r.y r.z) :
    TwoFourResiduePressure r := by
  rcases h with hxy | hxz | hyz
  · exact Or.inl ⟨hxy.1, hxy.2.1, hxy.2.2,
      twoFour_xy_rhs_pow_mod16_atlas r hxy.1 hxy.2.1⟩
  · exact Or.inr (Or.inl ⟨hxz.1, hxz.2.1, hxz.2.2,
      twoFour_xz_residue_atlas r hxz.1 hxz.2.1⟩)
  · exact Or.inr (Or.inr ⟨hyz.1, hyz.2.1, hyz.2.2,
      twoFour_yz_residue_atlas r hyz.1 hyz.2.1⟩)

#print axioms MCore.BealEffective.OpenMath.twoFour_xz_residue_atlas
#print axioms MCore.BealEffective.OpenMath.twoFour_yz_residue_atlas
#print axioms MCore.BealEffective.OpenMath.twoFour_xy_rhs_not_even_atlas
#print axioms MCore.BealEffective.OpenMath.twoFour_xy_rhs_pow_mod16_atlas
#print axioms MCore.BealEffective.OpenMath.twoFourPrime_forces_residue_pressure

end OpenMath
end BealEffective
end MCore
