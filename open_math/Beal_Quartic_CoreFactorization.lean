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

/-- Closed form of the recursive quotient at exponent two. -/
private theorem coreDiffQuot_two
    (c a : Nat) :
    CoreDiffQuot c a 2 = c + a := by
  simp [CoreDiffQuot, Nat.pow_succ, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/--
No odd prime divides both c-a and c^2+a^2 on x=z=4.
-/
theorem reduced_xz_four_sub_quad_odd_prime_disjoint
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ r.c - r.a ∧ p ∣ r.c ^ 2 + r.a ^ 2) := by
  intro h
  rcases h with ⟨hsub, hquad⟩
  have hac_lt : r.a < r.c := by
    have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.z := by
      simpa [Nat.add_comm] using r.equation
    exact core_right_same_exponent_gap r.b_pos (by simpa [hx, hz] using heq')
  have hac : r.a ≤ r.c := Nat.le_of_lt hac_lt
  have hfac2 := core_diff_factorization hac 2
  rw [coreDiffQuot_two] at hfac2
  have hprod : p ∣ (r.c - r.a) * (r.c + r.a) :=
    dvd_mul_right_local hsub
  have hdiffEq :
      r.c ^ 2 - r.a ^ 2 = (r.c - r.a) * (r.c + r.a) := by
    rw [← hfac2]
    simp
  have hdiff : p ∣ r.c ^ 2 - r.a ^ 2 := by
    rw [hdiffEq]
    exact hprod
  have h2a2 : p ∣ 2 * (r.a ^ 2) := by
    have hs : p ∣ (r.c ^ 2 + r.a ^ 2) - (r.c ^ 2 - r.a ^ 2) :=
      Nat.dvd_sub hquad hdiff
    have hsqle : r.a ^ 2 ≤ r.c ^ 2 := by
      rw [← hfac2]
      exact Nat.le_add_right _ _
    have hid :
        (r.c ^ 2 + r.a ^ 2) - (r.c ^ 2 - r.a ^ 2) =
          2 * (r.a ^ 2) := by
      omega
    simpa [hid] using hs
  have hpa2 : p ∣ r.a ^ 2 := by
    rcases prime_dvd_mul_local hp h2a2 with htwo | ha2
    · have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have heq : p = 2 := by omega
      exact False.elim (hp2 heq)
    · exact ha2
  have hpa : p ∣ r.a := prime_dvd_pow_reflect hp hpa2
  have hpc : p ∣ r.c := by
    have hs : p ∣ (r.c - r.a) + r.a := Nat.dvd_add hsub hpa
    simpa [Nat.sub_add_cancel hac] using hs
  exact (quarticPairwise r).2.1 ⟨p, hp.1, hpa, hpc⟩

/--
No odd prime divides both c+a and c^2+a^2 on x=z=4.
-/
theorem reduced_xz_four_add_quad_odd_prime_disjoint
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ r.c + r.a ∧ p ∣ r.c ^ 2 + r.a ^ 2) := by
  intro h
  rcases h with ⟨hadd, hquad⟩
  have hsq : p ∣ (r.c + r.a) * (r.c + r.a) :=
    dvd_mul_right_local hadd
  have hsumSq :
      (r.c + r.a) * (r.c + r.a) =
        r.c ^ 2 + 2 * r.c * r.a + r.a ^ 2 := by
    simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hfull : p ∣ r.c ^ 2 + 2 * r.c * r.a + r.a ^ 2 := by
    rw [← hsumSq]
    exact hsq
  have h2ca : p ∣ 2 * r.c * r.a := by
    have hs :
        p ∣ (r.c ^ 2 + 2 * r.c * r.a + r.a ^ 2) -
          (r.c ^ 2 + r.a ^ 2) :=
      Nat.dvd_sub hfull hquad
    have hid :
        (r.c ^ 2 + 2 * r.c * r.a + r.a ^ 2) -
          (r.c ^ 2 + r.a ^ 2) =
        2 * r.c * r.a := by
      omega
    simpa [hid] using hs
  rcases prime_dvd_mul_local hp h2ca with h2c | hpa
  · rcases prime_dvd_mul_local hp h2c with htwo | hpc
    · have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have heq : p = 2 := by omega
      exact hp2 heq
    ·
      have hpa' : p ∣ r.a := by
        have hs : p ∣ (r.c + r.a) - r.c := Nat.dvd_sub hadd hpc
        simpa using hs
      exact (quarticPairwise r).2.1 ⟨p, hp.1, hpa', hpc⟩
  ·
    have hpc : p ∣ r.c := by
      have hs : p ∣ (r.c + r.a) - r.a := Nat.dvd_sub hadd hpa
      simpa using hs
    exact (quarticPairwise r).2.1 ⟨p, hp.1, hpa, hpc⟩

/--
The three quartic blocks on x=z=4 have pairwise disjoint odd-prime support.
-/
theorem reduced_xz_four_three_block_odd_prime_separation
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ r.c - r.a ∧ p ∣ r.c + r.a) ∧
    ¬ (p ∣ r.c - r.a ∧ p ∣ r.c ^ 2 + r.a ^ 2) ∧
    ¬ (p ∣ r.c + r.a ∧ p ∣ r.c ^ 2 + r.a ^ 2) := by
  exact ⟨
    reduced_xz_four_linear_odd_prime_disjoint r hx hz hp hp2,
    reduced_xz_four_sub_quad_odd_prime_disjoint r hx hz hp hp2,
    reduced_xz_four_add_quad_odd_prime_disjoint r hx hz hp hp2
  ⟩

private theorem quartic_notEven_mod2_one
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

private theorem quarticExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c :=
  exactlyOneEven_of_pairwise (quarticData r) (quarticPairwise r)

/--
If a is the unique even base on x=z=4, all three quartic blocks are odd.
-/
theorem reduced_xz_four_a_even_blocks_odd
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (ha : Even r.a) :
    (r.c - r.a) % 2 = 1 ∧
    (r.c + r.a) % 2 = 1 ∧
    (r.c ^ 2 + r.a ^ 2) % 2 = 1 := by
  have hE := quarticExactlyOneEven r
  have hcOdd : r.c % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact (quartic_notEven_mod2_one r.c).mp hA.2.2
    · exact False.elim (hB.1 ha)
    · exact False.elim (hC.1 ha)
  have ha0 : r.a % 2 = 0 := Nat.mod_eq_zero_of_dvd ha
  constructor
  · rw [Nat.sub_mod]
    omega
  constructor
  · rw [Nat.add_mod, hcOdd, ha0]
    decide
  · rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod, hcOdd, ha0]
    decide

private theorem prime_ne_two_of_odd_divisor
    {p n : Nat}
    (hp : IsPrime p)
    (hnOdd : n % 2 = 1)
    (hpn : p ∣ n) :
    p ≠ 2 := by
  intro hp2
  subst p
  have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hpn
  omega

private theorem gcd_eq_one_of_no_common_prime
    {u v : Nat}
    (huPos : 0 < u)
    (hNo :
      ∀ p : Nat, IsPrime p → ¬ (p ∣ u ∧ p ∣ v)) :
    Nat.gcd u v = 1 := by
  by_contra hne
  have hgPos : 0 < Nat.gcd u v :=
    Nat.gcd_pos_of_pos_left v huPos
  have hgGt : 1 < Nat.gcd u v := by omega
  rcases primeDivisorProperty_proved (Nat.gcd u v) hgGt with
    ⟨p, hp, hpg⟩
  have hpu : p ∣ u := nat_dvd_trans hpg (Nat.gcd_dvd_left u v)
  have hpv : p ∣ v := nat_dvd_trans hpg (Nat.gcd_dvd_right u v)
  exact hNo p hp ⟨hpu, hpv⟩

/--
On x=z=4 with a even, the three quartic blocks are pairwise coprime.
This is the exact UFD-ready packet needed before perfect-power splitting.
-/
theorem reduced_xz_four_a_even_block_gcd_packet
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (ha : Even r.a) :
    Nat.gcd (r.c - r.a) (r.c + r.a) = 1 ∧
    Nat.gcd (r.c - r.a) (r.c ^ 2 + r.a ^ 2) = 1 ∧
    Nat.gcd (r.c + r.a) (r.c ^ 2 + r.a ^ 2) = 1 := by
  have hOdd := reduced_xz_four_a_even_blocks_odd r hx hz ha
  have hac_lt : r.a < r.c := by
    have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.z := by
      simpa [Nat.add_comm] using r.equation
    exact core_right_same_exponent_gap r.b_pos (by simpa [hx, hz] using heq')
  have hsubPos : 0 < r.c - r.a := Nat.zero_lt_sub_of_lt hac_lt
  have haddPos : 0 < r.c + r.a := Nat.add_pos_left r.c r.a_pos
  constructor
  · apply gcd_eq_one_of_no_common_prime hsubPos
    intro p hp hboth
    have hp2 : p ≠ 2 :=
      prime_ne_two_of_odd_divisor hp hOdd.1 hboth.1
    exact reduced_xz_four_linear_odd_prime_disjoint
      r hx hz hp hp2 hboth
  constructor
  · apply gcd_eq_one_of_no_common_prime hsubPos
    intro p hp hboth
    have hp2 : p ≠ 2 :=
      prime_ne_two_of_odd_divisor hp hOdd.1 hboth.1
    exact reduced_xz_four_sub_quad_odd_prime_disjoint
      r hx hz hp hp2 hboth
  · apply gcd_eq_one_of_no_common_prime haddPos
    intro p hp hboth
    have hp2 : p ≠ 2 :=
      prime_ne_two_of_odd_divisor hp hOdd.2.1 hboth.1
    exact reduced_xz_four_add_quad_odd_prime_disjoint
      r hx hz hp hp2 hboth

/--
Complete core-only quartic packet for the a-even x=z=4 orientation.
-/
structure XZFourAEvenCorePacket
    (r : ReducedPrimitiveCandidate) : Prop where
  hx : r.x = 4
  hz : r.z = 4
  ha : Even r.a
  factorization :
    r.b ^ r.y =
      (r.c - r.a) * ((r.c + r.a) * (r.c ^ 2 + r.a ^ 2))
  blocksOdd :
    (r.c - r.a) % 2 = 1 ∧
    (r.c + r.a) % 2 = 1 ∧
    (r.c ^ 2 + r.a ^ 2) % 2 = 1
  blocksCoprime :
    Nat.gcd (r.c - r.a) (r.c + r.a) = 1 ∧
    Nat.gcd (r.c - r.a) (r.c ^ 2 + r.a ^ 2) = 1 ∧
    Nat.gcd (r.c + r.a) (r.c ^ 2 + r.a ^ 2) = 1

def reduced_xz_four_a_even_core_packet
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (ha : Even r.a) :
    XZFourAEvenCorePacket r where
  hx := hx
  hz := hz
  ha := ha
  factorization := reduced_xz_four_exact_factorization r hx hz
  blocksOdd := reduced_xz_four_a_even_blocks_odd r hx hz ha
  blocksCoprime := reduced_xz_four_a_even_block_gcd_packet r hx hz ha

/--
Minimal UFD producer: a product of two coprime naturals which is an e-th
power splits into two e-th powers.
-/
def CoprimePairPowerSplitting : Prop :=
  ∀ A B b e : Nat,
    0 < e →
    Nat.gcd A B = 1 →
    b ^ e = A * B →
    ∃ u v : Nat, A = u ^ e ∧ B = v ^ e

private theorem gcd_mul_eq_one_of_pairwise_gcd
    {A B C : Nat}
    (hAB : Nat.gcd A B = 1)
    (hAC : Nat.gcd A C = 1) :
    Nat.gcd A (B * C) = 1 := by
  by_contra hne
  have hApos : 0 < A := by
    by_cases hA0 : A = 0
    · subst A
      simp at hAB
    · exact Nat.pos_of_ne_zero hA0
  have hgPos : 0 < Nat.gcd A (B * C) :=
    Nat.gcd_pos_of_pos_left (B * C) hApos
  have hgGt : 1 < Nat.gcd A (B * C) := by omega
  rcases primeDivisorProperty_proved (Nat.gcd A (B * C)) hgGt with
    ⟨p, hp, hpg⟩
  have hpA : p ∣ A :=
    nat_dvd_trans hpg (Nat.gcd_dvd_left A (B * C))
  have hpBC : p ∣ B * C :=
    nat_dvd_trans hpg (Nat.gcd_dvd_right A (B * C))
  rcases prime_dvd_mul_local hp hpBC with hpB | hpC
  · have hpG : p ∣ Nat.gcd A B := Nat.dvd_gcd hpA hpB
    rw [hAB] at hpG
    have hle : p ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hpG
    omega
  · have hpG : p ∣ Nat.gcd A C := Nat.dvd_gcd hpA hpC
    rw [hAC] at hpG
    have hle : p ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hpG
    omega

/-- The two-factor splitter is sufficient to construct the triple splitter. -/
theorem pairSplitter_implies_tripleSplitter
    (hPair : CoprimePairPowerSplitting) :
    CoprimeTriplePowerSplitting := by
  intro A B C b e he hAB hAC hBC hpow
  have hA_BC : Nat.gcd A (B * C) = 1 :=
    gcd_mul_eq_one_of_pairwise_gcd hAB hAC
  rcases hPair A (B * C) b e he hA_BC hpow with
    ⟨u, t, hA, hBCpow⟩
  rcases hPair B C t e he hBC hBCpow with
    ⟨v, w, hB, hC⟩
  exact ⟨u, v, w, hA, hB, hC⟩

/--
Generic UFD producer isolated from Beal:
a pairwise-coprime triple whose product is an e-th power splits into e-th
powers componentwise.
-/
def CoprimeTriplePowerSplitting : Prop :=
  ∀ A B C b e : Nat,
    0 < e →
    Nat.gcd A B = 1 →
    Nat.gcd A C = 1 →
    Nat.gcd B C = 1 →
    b ^ e = A * (B * C) →
    ∃ u v w : Nat,
      A = u ^ e ∧
      B = v ^ e ∧
      C = w ^ e

/--
The a-even x=z=4 branch reduces exactly to the generic coprime power splitter.
No Beal conclusion appears in this producer.
-/
theorem reduced_xz_four_a_even_power_forms_of_splitter
    (hSplit : CoprimeTriplePowerSplitting)
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (ha : Even r.a) :
    ∃ u v w : Nat,
      r.c - r.a = u ^ r.y ∧
      r.c + r.a = v ^ r.y ∧
      r.c ^ 2 + r.a ^ 2 = w ^ r.y := by
  have P := reduced_xz_four_a_even_core_packet r hx hz ha
  have hyPos : 0 < r.y :=
    Nat.lt_trans (by decide : 0 < 2) r.y_reduced.1
  exact hSplit
    (r.c - r.a)
    (r.c + r.a)
    (r.c ^ 2 + r.a ^ 2)
    r.b
    r.y
    hyPos
    P.blocksCoprime.1
    P.blocksCoprime.2.1
    P.blocksCoprime.2.2
    P.factorization

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
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_sub_quad_odd_prime_disjoint
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_add_quad_odd_prime_disjoint
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_three_block_odd_prime_separation
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_a_even_blocks_odd
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_a_even_block_gcd_packet
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_a_even_core_packet
#print axioms MCore.BealEffective.OpenMath.pairSplitter_implies_tripleSplitter
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_a_even_power_forms_of_splitter

end OpenMath
end BealEffective
end MCore
