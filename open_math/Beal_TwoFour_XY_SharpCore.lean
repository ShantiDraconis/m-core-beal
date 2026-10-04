import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem xys_pow_mod_congr
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

private theorem xys_notEven_mod2_one (n : Nat) :
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

private theorem xys_odd_residue16
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨
    n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by
  have hpar : (n % 16) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 16)).trans hn
  have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
  omega

private theorem xys_odd_residue8
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  have hpar : (n % 8) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  omega

private theorem xys_odd_fourth16
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 16 = 1 := by
  rcases xys_odd_residue16 hn with h | h | h | h | h | h | h | h
  all_goals
    have hc : n ^ 4 % 16 = (n % 16) ^ 4 % 16 := by
      apply xys_pow_mod_congr
      simp
    rw [hc, h]

private theorem xys_even_fourth16
    {n : Nat}
    (hn : Even n) :
    n ^ 4 % 16 = 0 := by
  rcases hn with ⟨k, hk⟩
  rw [hk]
  simp [Nat.mul_pow, Nat.mul_mod]

private theorem xys_odd_fourth8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  rcases xys_odd_residue8 hn with h | h | h | h
  all_goals
    have hc : n ^ 4 % 8 = (n % 8) ^ 4 % 8 := by
      apply xys_pow_mod_congr
      simp
    rw [hc, h]

private theorem xys_even_pow8
    {n e : Nat}
    (hn : Even n)
    (he : 2 < e) :
    n ^ e % 8 = 0 := by
  rcases hn with ⟨k, hk⟩
  obtain ⟨m, hm⟩ : ∃ m : Nat, e = m + 3 := by
    refine ⟨e - 3, ?_⟩
    omega
  rw [hk, hm]
  simp [Nat.pow_add, Nat.mul_pow, Nat.mul_mod,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private def xysData (r : ReducedPrimitiveCandidate) : BealData where
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

private theorem xysPairwise (r : ReducedPrimitiveCandidate) :
    PairwisePrimitive r.a r.b r.c := by
  constructor
  · intro h
    exact r.no_common (ab_pair_forces_common (xysData r) h)
  · constructor
    · intro h
      exact r.no_common (ac_pair_forces_common (xysData r) h)
    · intro h
      exact r.no_common (bc_pair_forces_common (xysData r) h)

private theorem xysExactlyOneEven (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c :=
  exactlyOneEven_of_pairwise (xysData r) (xysPairwise r)

private theorem xys_rhs_not_even
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    ¬ Even r.c := by
  intro hc
  have hE := xysExactlyOneEven r
  have haOdd : r.a % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact (xys_notEven_mod2_one r.a).mp hB.1
    · exact (xys_notEven_mod2_one r.a).mp hC.1
  have hbOdd : r.b % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact (xys_notEven_mod2_one r.b).mp hA.2.1
    · exact False.elim (hB.2.2 hc)
    · exact (xys_notEven_mod2_one r.b).mp hC.2.1
  have hA8 := xys_odd_fourth8 haOdd
  have hB8 := xys_odd_fourth8 hbOdd
  have hC8 := xys_even_pow8 hc r.z_reduced.1
  have hmod := congrArg (fun n : Nat => n % 8) r.equation
  have hbad : (1 + 1) % 8 = 0 := by
    simpa [hx, hy, Nat.add_mod, hA8, hB8, hC8] using hmod
  omega

private theorem xys_rhs_pow16
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    r.c ^ r.z % 16 = 1 := by
  have hcOdd : ¬ Even r.c := xys_rhs_not_even r hx hy
  have hE := xysExactlyOneEven r
  rcases hE with hA | hB | hC
  ·
    have hbOdd := (xys_notEven_mod2_one r.b).mp hA.2.1
    have hA16 := xys_even_fourth16 hA.1
    have hB16 := xys_odd_fourth16 hbOdd
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    have h : 1 = r.c ^ r.z % 16 := by
      simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
    exact h.symm
  ·
    have haOdd := (xys_notEven_mod2_one r.a).mp hB.1
    have hA16 := xys_odd_fourth16 haOdd
    have hB16 := xys_even_fourth16 hB.2.1
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    have h : 1 = r.c ^ r.z % 16 := by
      simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
    exact h.symm
  · exact False.elim (hcOdd hC.2.2)

private theorem xys_odd_exponent_repr
    {e : Nat}
    (he : e % 2 = 1) :
    ∃ k : Nat, e = 2 * k + 1 := by
  refine ⟨e / 2, ?_⟩
  have h := Nat.mod_add_div e 2
  rw [he] at h
  omega

private theorem xys_odd_square16
    {u : Nat}
    (hu : u % 2 = 1) :
    u ^ 2 % 16 = 1 := by
  rcases xys_odd_residue16 hu with h | h | h | h | h | h | h | h
  all_goals
    have hc : u ^ 2 % 16 = (u % 16) ^ 2 % 16 := by
      apply xys_pow_mod_congr
      simp
    rw [hc, h]
    decide

private theorem xys_odd_pow16_eq_base
    {u e : Nat}
    (hu : u % 2 = 1)
    (he : e % 2 = 1) :
    u ^ e % 16 = u % 16 := by
  rcases xys_odd_exponent_repr he with ⟨k, hk⟩
  have hs : u ^ 2 % 16 = 1 := xys_odd_square16 hu
  have hkpow : (u ^ 2) ^ k % 16 = 1 := by
    have hc := xys_pow_mod_congr
      (a := u ^ 2) (b := 1) (m := 16) (e := k) hs
    simpa using hc
  rw [hk, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hkpow]
  simp

/--
Odd base + odd exponent + power 1 mod16 forces base 1 mod16.
-/
theorem odd_pow_mod16_eq_one_forces_base_one_core
    {u e : Nat}
    (huOdd : u % 2 = 1)
    (heOdd : e % 2 = 1)
    (hpow : u ^ e % 16 = 1) :
    u % 16 = 1 := by
  have hbase := xys_odd_pow16_eq_base huOdd heOdd
  rw [hbase] at hpow
  exact hpow

/--
Sharp ORBIT-A residue: x=y=4 and z an odd prime force c = 1 modulo 16.
-/
theorem xy_four_prime_forces_c_mod16_one
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4)
    (hzPrime : OddPrimeExponent r.z) :
    r.c % 16 = 1 := by
  have hcOdd : r.c % 2 = 1 :=
    (xys_notEven_mod2_one r.c).mp (xys_rhs_not_even r hx hy)
  have hzOdd : r.z % 2 = 1 := by
    have hnot : ¬ 2 ∣ r.z := by
      intro h2
      rcases hzPrime.1.2 2 h2 with h1 | h2eq
      · cases h1
      · have hlt : 2 < 2 := by simpa [h2eq] using hzPrime.2
        exact Nat.lt_irrefl 2 hlt
    have hpos : 0 < r.z % 2 := Nat.emod_pos_of_not_dvd hnot
    have hlt : r.z % 2 < 2 := Nat.mod_lt r.z (by decide)
    omega
  exact odd_pow_mod16_eq_one_forces_base_one_core
    hcOdd hzOdd (xys_rhs_pow16 r hx hy)

#print axioms MCore.BealEffective.OpenMath.odd_pow_mod16_eq_one_forces_base_one_core
#print axioms MCore.BealEffective.OpenMath.xy_four_prime_forces_c_mod16_one

end OpenMath
end BealEffective
end MCore
