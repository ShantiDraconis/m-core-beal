import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem xy_pow_mod_congr
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

private theorem xy_notEven_mod2_one
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

private theorem xy_odd_residue16
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨
    n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by
  have hpar : (n % 16) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 16)).trans hn
  have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
  omega

private theorem xy_odd_exponent_repr
    {e : Nat}
    (he : e % 2 = 1) :
    ∃ k : Nat, e = 2 * k + 1 := by
  refine ⟨e / 2, ?_⟩
  have h := Nat.mod_add_div e 2
  rw [he] at h
  omega

/--
For an odd residue u mod 16 and odd exponent e, u^e = 1 mod 16 forces
u = 1 mod 16.  Core-only finite residue proof.
-/
theorem odd_pow_mod16_eq_one_forces_base_one_core
    {u e : Nat}
    (huOdd : u % 2 = 1)
    (heOdd : e % 2 = 1)
    (hpow : u ^ e % 16 = 1) :
    u % 16 = 1 := by
  rcases xy_odd_exponent_repr heOdd with ⟨k, hk⟩
  rcases xy_odd_residue16 huOdd with
    h | h | h | h | h | h | h | h
  · exact h
  all_goals
    have hc : u ^ e % 16 = (u % 16) ^ e % 16 := by
      apply xy_pow_mod_congr
      simp
    rw [hc, hk, h] at hpow
    simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod] at hpow
    omega

private def xyData (r : ReducedPrimitiveCandidate) : BealData where
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

private theorem xyPairwise
    (r : ReducedPrimitiveCandidate) :
    PairwisePrimitive r.a r.b r.c := by
  constructor
  · intro h
    exact r.no_common (ab_pair_forces_common (xyData r) h)
  · constructor
    · intro h
      exact r.no_common (ac_pair_forces_common (xyData r) h)
    · intro h
      exact r.no_common (bc_pair_forces_common (xyData r) h)

private theorem xyExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c :=
  exactlyOneEven_of_pairwise (xyData r) (xyPairwise r)

private theorem xy_odd_fourth16
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 16 = 1 := by
  rcases xy_odd_residue16 hn with h | h | h | h | h | h | h | h
  all_goals
    have hc : n ^ 4 % 16 = (n % 16) ^ 4 % 16 := by
      apply xy_pow_mod_congr
      simp
    rw [hc, h]

private theorem xy_even_fourth16
    {n : Nat}
    (hn : Even n) :
    n ^ 4 % 16 = 0 := by
  rcases hn with ⟨k, hk⟩
  rw [hk]
  simp [Nat.mul_pow, Nat.mul_mod]

/--
On the x=y=4 branch the right base c is odd and c^z = 1 mod 16.
-/
theorem xy_four_rhs_pow_mod16
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    r.c ^ r.z % 16 = 1 := by
  have hE := xyExactlyOneEven r
  rcases hE with hA | hB | hC
  ·
    have hbOdd : r.b % 2 = 1 := (xy_notEven_mod2_one r.b).mp hA.2.1
    have hA16 : r.a ^ 4 % 16 = 0 := xy_even_fourth16 hA.1
    have hB16 : r.b ^ 4 % 16 = 1 := xy_odd_fourth16 hbOdd
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
  ·
    have haOdd : r.a % 2 = 1 := (xy_notEven_mod2_one r.a).mp hB.1
    have hA16 : r.a ^ 4 % 16 = 1 := xy_odd_fourth16 haOdd
    have hB16 : r.b ^ 4 % 16 = 0 := xy_even_fourth16 hB.2.1
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
  ·
    have haOdd : r.a % 2 = 1 := (xy_notEven_mod2_one r.a).mp hC.1
    have hbOdd : r.b % 2 = 1 := (xy_notEven_mod2_one r.b).mp hC.2.1
    have hA8 : r.a ^ 4 % 8 = 1 := by
      have hpar : (r.a % 8) % 2 = 1 :=
        (Nat.mod_mod_of_dvd r.a (by decide : 2 ∣ 8)).trans haOdd
      have hlt : r.a % 8 < 8 := Nat.mod_lt r.a (by decide)
      have hres :
          r.a % 8 = 1 ∨ r.a % 8 = 3 ∨ r.a % 8 = 5 ∨ r.a % 8 = 7 := by
        omega
      rcases hres with h | h | h | h
      all_goals
        have hc : r.a ^ 4 % 8 = (r.a % 8) ^ 4 % 8 := by
          apply xy_pow_mod_congr
          simp
        rw [hc, h]
    have hB8 : r.b ^ 4 % 8 = 1 := by
      have hres :
          r.b % 8 = 1 ∨ r.b % 8 = 3 ∨ r.b % 8 = 5 ∨ r.b % 8 = 7 := by
        have hpar : (r.b % 8) % 2 = 1 :=
          (Nat.mod_mod_of_dvd r.b (by decide : 2 ∣ 8)).trans hbOdd
        have hlt : r.b % 8 < 8 := Nat.mod_lt r.b (by decide)
        omega
      rcases hres with h | h | h | h
      all_goals
        have hc : r.b ^ 4 % 8 = (r.b % 8) ^ 4 % 8 := by
          apply xy_pow_mod_congr
          simp
        rw [hc, h]
    have hC8 : r.c ^ r.z % 8 = 0 := by
      rcases hC.2.2 with ⟨k, hk⟩
      obtain ⟨m, hm⟩ : ∃ m : Nat, r.z = m + 3 := by
        refine ⟨r.z - 3, ?_⟩
        omega
      rw [hk, hm]
      simp [Nat.pow_add, Nat.mul_pow, Nat.mul_mod]
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    have hbad : (1 + 1) % 8 = 0 := by
      simpa [hx, hy, Nat.add_mod, hA8, hB8, hC8] using hmod
    simp at hbad

/--
Sharp ORBIT-A residue: for x=y=4 and z an odd prime exponent, c itself is
1 modulo 16.
-/
theorem xy_four_prime_forces_c_mod16_one
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4)
    (hzPrime : OddPrimeExponent r.z) :
    r.c % 16 = 1 := by
  have hcNotEven : ¬ Even r.c := by
    intro hc
    have hE := xyExactlyOneEven r
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact False.elim (hB.2.2 hc)
    ·
      have haOdd : r.a % 2 = 1 := (xy_notEven_mod2_one r.a).mp hC.1
      have hbOdd : r.b % 2 = 1 := (xy_notEven_mod2_one r.b).mp hC.2.1
      have hA8 : r.a ^ 4 % 8 = 1 := by
        have hres :
            r.a % 8 = 1 ∨ r.a % 8 = 3 ∨ r.a % 8 = 5 ∨ r.a % 8 = 7 := by
          have hpar : (r.a % 8) % 2 = 1 :=
            (Nat.mod_mod_of_dvd r.a (by decide : 2 ∣ 8)).trans haOdd
          have hlt : r.a % 8 < 8 := Nat.mod_lt r.a (by decide)
          omega
        rcases hres with h | h | h | h
        all_goals
          have hcg : r.a ^ 4 % 8 = (r.a % 8) ^ 4 % 8 := by
            apply xy_pow_mod_congr
            simp
          rw [hcg, h]
      have hB8 : r.b ^ 4 % 8 = 1 := by
        have hres :
            r.b % 8 = 1 ∨ r.b % 8 = 3 ∨ r.b % 8 = 5 ∨ r.b % 8 = 7 := by
          have hpar : (r.b % 8) % 2 = 1 :=
            (Nat.mod_mod_of_dvd r.b (by decide : 2 ∣ 8)).trans hbOdd
          have hlt : r.b % 8 < 8 := Nat.mod_lt r.b (by decide)
          omega
        rcases hres with h | h | h | h
        all_goals
          have hcg : r.b ^ 4 % 8 = (r.b % 8) ^ 4 % 8 := by
            apply xy_pow_mod_congr
            simp
          rw [hcg, h]
      have hC8 : r.c ^ r.z % 8 = 0 := by
        rcases hc with ⟨k, hk⟩
        obtain ⟨m, hm⟩ : ∃ m : Nat, r.z = m + 3 := by
          refine ⟨r.z - 3, ?_⟩
          omega
        rw [hk, hm]
        simp [Nat.pow_add, Nat.mul_pow, Nat.mul_mod]
      have hmod := congrArg (fun n : Nat => n % 8) r.equation
      have hbad : (1 + 1) % 8 = 0 := by
        simpa [hx, hy, Nat.add_mod, hA8, hB8, hC8] using hmod
      simp at hbad
  have hcOdd : r.c % 2 = 1 :=
    (xy_notEven_mod2_one r.c).mp hcNotEven
  have hzOdd : r.z % 2 = 1 := by
    have hnot : ¬ 2 ∣ r.z := by
      intro h2
      rcases hzPrime.1.2 2 h2 with h1 | hz2
      · cases h1
      · have : 2 < 2 := by simpa [hz2] using hzPrime.2
        exact Nat.lt_irrefl 2 this
    have hpos : 0 < r.z % 2 := Nat.emod_pos_of_not_dvd hnot
    have hlt : r.z % 2 < 2 := Nat.mod_lt r.z (by decide)
    omega
  exact odd_pow_mod16_eq_one_forces_base_one_core
    hcOdd hzOdd (xy_four_rhs_pow_mod16 r hx hy)

#print axioms MCore.BealEffective.OpenMath.odd_pow_mod16_eq_one_forces_base_one_core
#print axioms MCore.BealEffective.OpenMath.xy_four_rhs_pow_mod16
#print axioms MCore.BealEffective.OpenMath.xy_four_prime_forces_c_mod16_one

end OpenMath
end BealEffective
end MCore
