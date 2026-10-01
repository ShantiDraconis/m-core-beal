import Mathlib.Data.Nat.Factorization.Basic
import MCore.BealQuarticValuationPacket

namespace MCore

/--
If every prime-factor multiplicity of a nonzero natural number n is divisible
by e>0, then n is an exact e-th power.
-/
theorem exists_eq_pow_of_factorization_multiples
    {n e : Nat}
    (hn : n ≠ 0)
    (he : 0 < e)
    (hdiv : ∀ p : Nat, e ∣ n.factorization p) :
    ∃ m : Nat, n = m ^ e := by
  let f := n.factorization.mapRange (· / e) <| by simp
  have hf : n.factorization = e • f := by
    ext p
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply,
      Nat.mul_div_cancel' (hdiv p)]
  have hf0 : f 0 = 0 := by
    simpa [he.ne'] using congr($hf 0)
  refine ⟨f.prod (· ^ ·), Nat.factorization_inj hn (by simp [hf0]) ?_⟩
  rw [Nat.factorization_pow]
  exact hf.trans <|
    congrArg (fun g : Nat →₀ Nat => e • g)
      (n.factorization_prod_pow_eq_self_of_le_factorization
        (hf ▸ le_self_nsmul zero_le (by omega)))

/--
Odd-part perfect-power reconstruction.
If every odd prime q dividing n has q-adic multiplicity divisible by e, then
the odd part ordCompl[2] n is an exact e-th power.
-/
theorem oddPart_eq_pow_of_odd_prime_factorization_multiples
    {n e : Nat}
    (hn : n ≠ 0)
    (he : 0 < e)
    (hodd :
      ∀ q : Nat,
        IsPrime q →
        q ≠ 2 →
        q ∣ n →
        e ∣ n.factorization q) :
    ∃ m : Nat, Nat.ordCompl 2 n = m ^ e := by
  have hodd0 : Nat.ordCompl 2 n ≠ 0 :=
    (Nat.ordCompl_pos 2 (Nat.pos_of_ne_zero hn)).ne'
  apply exists_eq_pow_of_factorization_multiples hodd0 he
  intro q
  rw [Nat.factorization_ordCompl]
  by_cases hq2 : q = 2
  · subst q
    simp
  by_cases hqPrime : IsPrime q
  · by_cases hqdvd : q ∣ n
    · have hm := hodd q hqPrime hq2 hqdvd
      simpa [Finsupp.erase_apply, hq2] using hm
    · have hz : n.factorization q = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hqdvd
      simp [Finsupp.erase_apply, hq2, hz]
  · have hz : n.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_prime n hqPrime
    simp [Finsupp.erase_apply, hq2, hz]

/--
On x=z=4, the odd part of c-a is an exact y-th power.
-/
theorem T59_xz_four_oddPart_sub_is_power
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4) :
    ∃ u : Nat, Nat.ordCompl 2 (d.c - d.a) = u ^ d.y := by
  have hca_lt : d.a < d.c := by
    have heq' : d.b ^ d.y + d.a ^ d.x = d.c ^ d.z := by
      simpa [Nat.add_comm] using d.equation
    exact T21_right_same_exponent_gap d.b_pos heq' (by simpa [hx, hz])
  have hn : d.c - d.a ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_sub_of_lt hca_lt)
  have he : 0 < d.y :=
    Nat.lt_trans (by decide : 0 < 2) d.y_reduced.1
  apply oddPart_eq_pow_of_odd_prime_factorization_multiples hn he
  intro q hq hq2 hqdvd
  exact T59_xz_four_sub_factorization_multiple d hx hz hq hq2 hqdvd

/-- On x=z=4, the odd part of c+a is an exact y-th power. -/
theorem T59_xz_four_oddPart_add_is_power
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4) :
    ∃ v : Nat, Nat.ordCompl 2 (d.c + d.a) = v ^ d.y := by
  have hn : d.c + d.a ≠ 0 :=
    Nat.ne_of_gt (Nat.add_pos_left d.c d.a_pos)
  have he : 0 < d.y :=
    Nat.lt_trans (by decide : 0 < 2) d.y_reduced.1
  apply oddPart_eq_pow_of_odd_prime_factorization_multiples hn he
  intro q hq hq2 hqdvd
  exact T59_xz_four_add_factorization_multiple d hx hz hq hq2 hqdvd

/-- On x=z=4, the odd part of c^2+a^2 is an exact y-th power. -/
theorem T59_xz_four_oddPart_quad_is_power
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4) :
    ∃ w : Nat, Nat.ordCompl 2 (d.c ^ 2 + d.a ^ 2) = w ^ d.y := by
  have hn : d.c ^ 2 + d.a ^ 2 ≠ 0 := by
    have ha2 : 0 < d.a ^ 2 := Nat.pow_pos d.a_pos
    exact Nat.ne_of_gt (Nat.add_pos_right _ ha2)
  have he : 0 < d.y :=
    Nat.lt_trans (by decide : 0 < 2) d.y_reduced.1
  apply oddPart_eq_pow_of_odd_prime_factorization_multiples hn he
  intro q hq hq2 hqdvd
  exact T59_xz_four_quad_factorization_multiple d hx hz hq hq2 hqdvd

/-- Symmetric odd-part perfect-power laws for y=z=4. -/
theorem T59_yz_four_oddPart_sub_is_power
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4) :
    ∃ u : Nat, Nat.ordCompl 2 (d.c - d.b) = u ^ d.x := by
  have hbc_lt : d.b < d.c :=
    T21_right_same_exponent_gap d.a_pos d.equation (by simpa [hy, hz])
  have hn : d.c - d.b ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_sub_of_lt hbc_lt)
  have he : 0 < d.x :=
    Nat.lt_trans (by decide : 0 < 2) d.x_reduced.1
  apply oddPart_eq_pow_of_odd_prime_factorization_multiples hn he
  intro q hq hq2 hqdvd
  exact T59_yz_four_sub_factorization_multiple d hy hz hq hq2 hqdvd

theorem T59_yz_four_oddPart_add_is_power
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4) :
    ∃ v : Nat, Nat.ordCompl 2 (d.c + d.b) = v ^ d.x := by
  have hn : d.c + d.b ≠ 0 :=
    Nat.ne_of_gt (Nat.add_pos_left d.c d.b_pos)
  have he : 0 < d.x :=
    Nat.lt_trans (by decide : 0 < 2) d.x_reduced.1
  apply oddPart_eq_pow_of_odd_prime_factorization_multiples hn he
  intro q hq hq2 hqdvd
  exact T59_yz_four_add_factorization_multiple d hy hz hq hq2 hqdvd

theorem T59_yz_four_oddPart_quad_is_power
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4) :
    ∃ w : Nat, Nat.ordCompl 2 (d.c ^ 2 + d.b ^ 2) = w ^ d.x := by
  have hn : d.c ^ 2 + d.b ^ 2 ≠ 0 := by
    have hb2 : 0 < d.b ^ 2 := Nat.pow_pos d.b_pos
    exact Nat.ne_of_gt (Nat.add_pos_right _ hb2)
  have he : 0 < d.x :=
    Nat.lt_trans (by decide : 0 < 2) d.x_reduced.1
  apply oddPart_eq_pow_of_odd_prime_factorization_multiples hn he
  intro q hq hq2 hqdvd
  exact T59_yz_four_quad_factorization_multiple d hy hz hq hq2 hqdvd

#print axioms MCore.exists_eq_pow_of_factorization_multiples
#print axioms MCore.oddPart_eq_pow_of_odd_prime_factorization_multiples
#print axioms MCore.T59_xz_four_oddPart_sub_is_power
#print axioms MCore.T59_xz_four_oddPart_add_is_power
#print axioms MCore.T59_xz_four_oddPart_quad_is_power
#print axioms MCore.T59_yz_four_oddPart_sub_is_power
#print axioms MCore.T59_yz_four_oddPart_add_is_power
#print axioms MCore.T59_yz_four_oddPart_quad_is_power

end MCore
