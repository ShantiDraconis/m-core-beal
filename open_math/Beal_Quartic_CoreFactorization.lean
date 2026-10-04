import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

/-- Recursive quotient: b^n + (c-b)Q_n(c,b) = c^n when b ≤ c. -/
def CoreDiffQuot (c b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => c ^ n + b * CoreDiffQuot c b n

theorem core_diff_factorization
    {b c : Nat}
    (hbc : b ≤ c) :
    ∀ n : Nat, b ^ n + (c - b) * CoreDiffQuot c b n = c ^ n := by
  intro n
  induction n with
  | zero =>
      simp [CoreDiffQuot]
  | succ n ih =>
      change b ^ (n + 1) + (c - b) * (c ^ n + b * CoreDiffQuot c b n) =
        c ^ (n + 1)
      rw [Nat.pow_succ, Nat.pow_succ]
      calc
        b ^ n * b + (c - b) * (c ^ n + b * CoreDiffQuot c b n)
            = b * (b ^ n + (c - b) * CoreDiffQuot c b n) +
                (c - b) * c ^ n := by
                simp [Nat.left_distrib, Nat.right_distrib, Nat.mul_assoc,
                  Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm]
        _ = b * c ^ n + (c - b) * c ^ n := by rw [ih]
        _ = (b + (c - b)) * c ^ n := by rw [Nat.add_mul]
        _ = c * c ^ n := by rw [Nat.add_comm b, Nat.sub_add_cancel hbc]
        _ = c ^ n * c := Nat.mul_comm _ _

theorem core_right_same_exponent_gap
    {a b c x n : Nat}
    (ha : 0 < a)
    (heq : a ^ x + b ^ n = c ^ n) :
    b < c := by
  have hax : 0 < a ^ x := Nat.pow_pos ha
  have hp : b ^ n < c ^ n := by
    rw [← heq]
    exact Nat.lt_add_of_pos_left hax
  match Nat.lt_or_ge b c with
  | Or.inl h => exact h
  | Or.inr h =>
      have hpow : c ^ n ≤ b ^ n := Nat.pow_le_pow_left h n
      exact False.elim ((Nat.not_le_of_gt hp) hpow)

theorem reduced_y_eq_z_exact_factor
    (r : ReducedPrimitiveCandidate)
    (hyz : r.y = r.z) :
    r.a ^ r.x = (r.c - r.b) * CoreDiffQuot r.c r.b r.y := by
  have hbc_lt : r.b < r.c := by
    apply core_right_same_exponent_gap r.a_pos
    simpa [hyz] using r.equation
  have hbc : r.b ≤ r.c := Nat.le_of_lt hbc_lt
  have hfac := core_diff_factorization hbc r.y
  have hleft : r.b ^ r.y + r.a ^ r.x = r.c ^ r.y := by
    simpa [Nat.add_comm, hyz] using r.equation
  have hsum :
      r.b ^ r.y + r.a ^ r.x =
        r.b ^ r.y + (r.c - r.b) * CoreDiffQuot r.c r.b r.y :=
    hleft.trans hfac.symm
  exact Nat.add_left_cancel hsum

theorem reduced_x_eq_z_exact_factor
    (r : ReducedPrimitiveCandidate)
    (hxz : r.x = r.z) :
    r.b ^ r.y = (r.c - r.a) * CoreDiffQuot r.c r.a r.x := by
  have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.x := by
    simpa [Nat.add_comm, hxz] using r.equation
  have hac_lt : r.a < r.c :=
    core_right_same_exponent_gap r.b_pos heq'
  have hac : r.a ≤ r.c := Nat.le_of_lt hac_lt
  have hfac := core_diff_factorization hac r.x
  have hsum :
      r.a ^ r.x + r.b ^ r.y =
        r.a ^ r.x + (r.c - r.a) * CoreDiffQuot r.c r.a r.x :=
    r.equation.trans (by simpa [hxz] using hfac.symm)
  exact Nat.add_left_cancel hsum

/-- Closed form of the recursive quotient at exponent four. -/
theorem coreDiffQuot_four
    (c a : Nat) :
    CoreDiffQuot c a 4 =
      (c + a) * (c ^ 2 + a ^ 2) := by
  simp [CoreDiffQuot, Nat.pow_succ, Nat.add_mul, Nat.mul_add,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/--
Exact quartic factorization in the x=z=4 orientation:
  b^y = (c-a)(c+a)(c^2+a^2).
-/
theorem reduced_xz_four_exact_factorization
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4) :
    r.b ^ r.y =
      (r.c - r.a) * ((r.c + r.a) * (r.c ^ 2 + r.a ^ 2)) := by
  have hEq := reduced_x_eq_z_exact_factor r (hx.trans hz.symm)
  rw [hx, coreDiffQuot_four] at hEq
  exact hEq

/--
Symmetric exact quartic factorization in the y=z=4 orientation.
-/
theorem reduced_yz_four_exact_factorization
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4) :
    r.a ^ r.x =
      (r.c - r.b) * ((r.c + r.b) * (r.c ^ 2 + r.b ^ 2)) := by
  have hEq := reduced_y_eq_z_exact_factor r (hy.trans hz.symm)
  rw [hy, coreDiffQuot_four] at hEq
  exact hEq

private theorem dvd_mul_right_local
    {p a b : Nat}
    (h : p ∣ a) :
    p ∣ a * b := by
  rcases h with ⟨k, hk⟩
  refine ⟨k * b, ?_⟩
  rw [hk]
  simp [Nat.mul_assoc]

private theorem dvd_mul_left_local
    {p a b : Nat}
    (h : p ∣ b) :
    p ∣ a * b := by
  rcases h with ⟨k, hk⟩
  refine ⟨a * k, ?_⟩
  rw [hk]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private def quarticData (r : ReducedPrimitiveCandidate) : BealData where
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

private theorem quarticPairwise
    (r : ReducedPrimitiveCandidate) :
    PairwisePrimitive r.a r.b r.c := by
  constructor
  · intro h
    exact r.no_common (ab_pair_forces_common (quarticData r) h)
  · constructor
    · intro h
      exact r.no_common (ac_pair_forces_common (quarticData r) h)
    · intro h
      exact r.no_common (bc_pair_forces_common (quarticData r) h)

/-- Every prime dividing c-a on x=z=4 divides b. -/
theorem reduced_xz_four_sub_prime_supports_b
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c - r.a) :
    p ∣ r.b := by
  have hfac := reduced_xz_four_exact_factorization r hx hz
  have hpow : p ∣ r.b ^ r.y := by
    rw [hfac]
    exact dvd_mul_right_local hdiv
  exact prime_dvd_pow_reflect hp hpow

/-- Every prime dividing c+a on x=z=4 divides b. -/
theorem reduced_xz_four_add_prime_supports_b
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c + r.a) :
    p ∣ r.b := by
  have hfac := reduced_xz_four_exact_factorization r hx hz
  have hinner : p ∣ (r.c + r.a) * (r.c ^ 2 + r.a ^ 2) :=
    dvd_mul_right_local hdiv
  have hpow : p ∣ r.b ^ r.y := by
    rw [hfac]
    exact dvd_mul_left_local hinner
  exact prime_dvd_pow_reflect hp hpow

/-- Every prime dividing c^2+a^2 on x=z=4 divides b. -/
theorem reduced_xz_four_quad_prime_supports_b
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c ^ 2 + r.a ^ 2) :
    p ∣ r.b := by
  have hfac := reduced_xz_four_exact_factorization r hx hz
  have hinner : p ∣ (r.c + r.a) * (r.c ^ 2 + r.a ^ 2) :=
    dvd_mul_left_local hdiv
  have hpow : p ∣ r.b ^ r.y := by
    rw [hfac]
    exact dvd_mul_left_local hinner
  exact prime_dvd_pow_reflect hp hpow

/--
No odd prime divides both c-a and c+a on x=z=4.
-/ 
theorem reduced_xz_four_linear_odd_prime_disjoint
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ r.c - r.a ∧ p ∣ r.c + r.a) := by
  intro h
  rcases h with ⟨hminus, hplus⟩
  have hac_lt : r.a < r.c := by
    have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.z := by
      simpa [Nat.add_comm] using r.equation
    exact core_right_same_exponent_gap r.b_pos (by simpa [hx, hz] using heq')
  have hac : r.a ≤ r.c := Nat.le_of_lt hac_lt
  have h2a : p ∣ 2 * r.a := by
    have hsub : p ∣ (r.c + r.a) - (r.c - r.a) :=
      Nat.dvd_sub hplus hminus
    have hid : (r.c + r.a) - (r.c - r.a) = 2 * r.a := by
      omega
    simpa [hid] using hsub
  have hpa : p ∣ r.a := by
    rcases prime_dvd_mul_local hp h2a with htwo | ha
    · have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have heq : p = 2 := by omega
      exact False.elim (hp2 heq)
    · exact ha
  have hpc : p ∣ r.c := by
    have hsub : p ∣ (r.c + r.a) - r.a :=
      Nat.dvd_sub hplus hpa
    simpa using hsub
  exact (quarticPairwise r).2.1 ⟨p, hp.1, hpa, hpc⟩

/-- Symmetric prime-support statements on y=z=4. -/
theorem reduced_yz_four_sub_prime_supports_a
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c - r.b) :
    p ∣ r.a := by
  have hfac := reduced_yz_four_exact_factorization r hy hz
  have hpow : p ∣ r.a ^ r.x := by
    rw [hfac]
    exact dvd_mul_right_local hdiv
  exact prime_dvd_pow_reflect hp hpow

theorem reduced_yz_four_add_prime_supports_a
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c + r.b) :
    p ∣ r.a := by
  have hfac := reduced_yz_four_exact_factorization r hy hz
  have hinner : p ∣ (r.c + r.b) * (r.c ^ 2 + r.b ^ 2) :=
    dvd_mul_right_local hdiv
  have hpow : p ∣ r.a ^ r.x := by
    rw [hfac]
    exact dvd_mul_left_local hinner
  exact prime_dvd_pow_reflect hp hpow

theorem reduced_yz_four_quad_prime_supports_a
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c ^ 2 + r.b ^ 2) :
    p ∣ r.a := by
  have hfac := reduced_yz_four_exact_factorization r hy hz
  have hinner : p ∣ (r.c + r.b) * (r.c ^ 2 + r.b ^ 2) :=
    dvd_mul_left_local hdiv
  have hpow : p ∣ r.a ^ r.x := by
    rw [hfac]
    exact dvd_mul_left_local hinner
  exact prime_dvd_pow_reflect hp hpow

#print axioms MCore.BealEffective.OpenMath.core_diff_factorization
#print axioms MCore.BealEffective.OpenMath.core_right_same_exponent_gap
#print axioms MCore.BealEffective.OpenMath.reduced_x_eq_z_exact_factor
#print axioms MCore.BealEffective.OpenMath.reduced_y_eq_z_exact_factor
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_exact_factorization
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_exact_factorization
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_sub_prime_supports_b
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_add_prime_supports_b
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_quad_prime_supports_b
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_linear_odd_prime_disjoint
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_sub_prime_supports_a
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_add_prime_supports_a
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_quad_prime_supports_a

end OpenMath
end BealEffective
end MCore
