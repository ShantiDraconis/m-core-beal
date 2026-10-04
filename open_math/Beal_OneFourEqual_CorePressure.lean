import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private def ofepData (r : ReducedPrimitiveCandidate) : BealData where
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

private theorem ofepExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c := by
  have hpw : PairwisePrimitive r.a r.b r.c := by
    constructor
    · intro h
      exact r.no_common (ab_pair_forces_common (ofepData r) h)
    · constructor
      · intro h
        exact r.no_common (ac_pair_forces_common (ofepData r) h)
      · intro h
        exact r.no_common (bc_pair_forces_common (ofepData r) h)
  exact exactlyOneEven_of_pairwise (ofepData r) hpw

private theorem ofepNotEven_mod2_one
    (n : Nat) :
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

private theorem ofepOddResidue8
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  have hpar : (n % 8) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  omega

private theorem ofepOddFourth8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  rcases ofepOddResidue8 hn with h | h | h | h
  all_goals simp [Nat.pow_mod, h]

private theorem ofepEvenPow8
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

/--
Concrete residue consequences for x=4, y=z=p.
No modularity or conductor theorem is assumed.
-/
def OneFourEqualXPressure
    (r : ReducedPrimitiveCandidate) (p : Nat) : Prop :=
  (Even r.a → r.b ^ p % 8 = r.c ^ p % 8) ∧
  (Even r.b → r.c ^ p % 8 = 1) ∧
  (Even r.c → r.b ^ p % 8 = 7)

/-- Produce the x=4 residue pressure directly from the Beal equation. -/
theorem oneFourEqual_x_pressure
    (r : ReducedPrimitiveCandidate)
    (p : Nat)
    (hx : r.x = 4)
    (hy : r.y = p)
    (hz : r.z = p)
    (hp : OddPrimeExponent p) :
    OneFourEqualXPressure r p := by
  have hE := ofepExactlyOneEven r
  constructor
  · intro ha
    have hA8 : r.a ^ 4 % 8 = 0 := by
      rcases ha with ⟨k, rfl⟩
      simp [mul_pow, Nat.mul_mod]
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    rw [hx, hy, hz, Nat.add_mod, hA8] at hmod
    omega
  constructor
  · intro hb
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (ofepNotEven_mod2_one r.a).mp hB.1
      · exact False.elim (hC.2.1 hb)
    have hA8 : r.a ^ 4 % 8 = 1 := ofepOddFourth8 haOdd
    have hB8 : r.b ^ p % 8 = 0 := ofepEvenPow8 hb hp.2
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    rw [hx, hy, hz, Nat.add_mod, hA8, hB8] at hmod
    omega
  · intro hc
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (ofepNotEven_mod2_one r.a).mp hC.1
    have hA8 : r.a ^ 4 % 8 = 1 := ofepOddFourth8 haOdd
    have hC8 : r.c ^ p % 8 = 0 := ofepEvenPow8 hc hp.2
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    rw [hx, hy, hz, Nat.add_mod, hA8, hC8] at hmod
    omega

/--
Concrete pressure payload for all three placements of the single exponent 4.
The payload is strictly arithmetic and is produced from the candidate.
-/
def OneFourEqualResiduePressure (r : ReducedPrimitiveCandidate) : Prop :=
  (∃ p, OddPrimeExponent p ∧ r.x = 4 ∧ r.y = p ∧ r.z = p ∧
      OneFourEqualXPressure r p) ∨
  (∃ p, OddPrimeExponent p ∧ r.y = 4 ∧ r.x = p ∧ r.z = p) ∨
  (∃ p, OddPrimeExponent p ∧ r.z = 4 ∧ r.x = p ∧ r.y = p)

/--
The x=4 branch of OneFourEqualPrimes is now materially compressed to residue
pressure; the other two orientations remain explicit rather than hidden.
-/
theorem oneFourEqualPrimes_forces_x_pressure_or_other_orientation
    (r : ReducedPrimitiveCandidate)
    (h : OneFourEqualPrimes r.x r.y r.z) :
    OneFourEqualResiduePressure r := by
  rcases h with hx | hy | hz
  · rcases hx with ⟨hx4, hp, hzy⟩
    exact Or.inl ⟨r.y, hp, hx4, rfl, hzy,
      oneFourEqual_x_pressure r r.y hx4 rfl hzy hp⟩
  · rcases hy with ⟨hy4, hp, hzx⟩
    exact Or.inr (Or.inl ⟨r.x, hp, hy4, rfl, hzx⟩)
  · rcases hz with ⟨hz4, hp, hyx⟩
    exact Or.inr (Or.inr ⟨r.x, hp, hz4, rfl, hyx⟩)

#print axioms MCore.BealEffective.OpenMath.oneFourEqual_x_pressure
#print axioms MCore.BealEffective.OpenMath.oneFourEqualPrimes_forces_x_pressure_or_other_orientation

end OpenMath
end BealEffective
end MCore
