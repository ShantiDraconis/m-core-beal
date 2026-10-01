import MCore.BealQuarticPurePowerParametrization

namespace MCore

/--
Elementary square identity behind the generalized-Fermat reduction:
(c-a)^2 + (c+a)^2 = 2(c^2+a^2), when a <= c.
-/
theorem quartic_linear_square_sum
    {a c : Nat}
    (hac : a ≤ c) :
    (c - a) ^ 2 + (c + a) ^ 2 = 2 * (c ^ 2 + a ^ 2) := by
  omega

/--
On the x=z=4, a-even residual branch, the pure-power parametrization yields

  u^(2y) + v^(2y) = 2*w^y.
-/
theorem T59_xz_four_a_even_generalized_fermat
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    ∃ u v w : Nat,
      d.c - d.a = u ^ d.y ∧
      d.c + d.a = v ^ d.y ∧
      d.c ^ 2 + d.a ^ 2 = w ^ d.y ∧
      u ^ (2 * d.y) + v ^ (2 * d.y) = 2 * w ^ d.y := by
  rcases T59_xz_four_a_even_base_product d hx hz haEven with
    ⟨u,v,w,hsub,hadd,hquad,hb⟩
  have hac_lt : d.a < d.c := by
    have heq' : d.b ^ d.y + d.a ^ d.x = d.c ^ d.z := by
      simpa [Nat.add_comm] using d.equation
    exact T21_right_same_exponent_gap d.b_pos heq' (by simpa [hx, hz])
  have hid := quartic_linear_square_sum (Nat.le_of_lt hac_lt)
  rw [hsub, hadd, hquad] at hid
  have hp1 : (u ^ d.y) ^ 2 = u ^ (2 * d.y) := by
    rw [← pow_mul]
    ring_nf
  have hp2 : (v ^ d.y) ^ 2 = v ^ (2 * d.y) := by
    rw [← pow_mul]
    ring_nf
  rw [hp1, hp2] at hid
  exact ⟨u,v,w,hsub,hadd,hquad,hid⟩

/--
Equivalent generalized-Fermat form:
  (u^2)^y + (v^2)^y = 2*w^y.
-/
theorem T59_xz_four_a_even_generalized_fermat_squared_bases
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    ∃ X Y Z : Nat,
      X ^ d.y + Y ^ d.y = 2 * Z ^ d.y := by
  rcases T59_xz_four_a_even_generalized_fermat d hx hz haEven with
    ⟨u,v,w,_,_,_,h⟩
  refine ⟨u^2, v^2, w, ?_⟩
  simpa [pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/--
The two pure-power linear bases u and v are coprime.
Any common prime would divide both c-a and c+a, impossible for odd primes;
2 cannot divide either factor because both are odd on this orientation.
-/
theorem T59_xz_four_a_even_uv_coprime
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    ∃ u v : Nat,
      d.c - d.a = u ^ d.y ∧
      d.c + d.a = v ^ d.y ∧
      Nat.Coprime u v := by
  rcases T59_xz_four_a_even_linear_factors_are_powers d hx hz haEven with
    ⟨⟨u,hu⟩,⟨v,hv⟩⟩
  refine ⟨u,v,hu,hv,?_⟩
  apply Nat.coprime_iff_gcd_eq_one.mpr
  by_contra hg
  have hgone : 1 < Nat.gcd u v := by
    have hpos : 0 < Nat.gcd u v := by
      have huPos : 0 < u := by
        have hsubPos : 0 < d.c - d.a := by
          have hac_lt : d.a < d.c := by
            have heq' : d.b ^ d.y + d.a ^ d.x = d.c ^ d.z := by
              simpa [Nat.add_comm] using d.equation
            exact T21_right_same_exponent_gap d.b_pos heq' (by simpa [hx, hz])
          exact Nat.zero_lt_sub_of_lt hac_lt
        rw [hu] at hsubPos
        exact Nat.pos_of_pow_pos _ hsubPos
      exact Nat.gcd_pos_of_pos_left _ huPos
    omega
  obtain ⟨q,hqPrime,hqg⟩ := Nat.exists_prime_and_dvd hgone
  have hqu : q ∣ u := Nat.dvd_trans hqg (Nat.gcd_dvd_left u v)
  have hqv : q ∣ v := Nat.dvd_trans hqg (Nat.gcd_dvd_right u v)
  have hqsub : q ∣ d.c - d.a := by
    rw [hu]
    exact dvd_pow_self q d.y hqu
  have hqadd : q ∣ d.c + d.a := by
    rw [hv]
    exact dvd_pow_self q d.y hqv
  have hq2 : q ≠ 2 := by
    intro h2
    subst q
    have hodd := T59_xz_four_a_even_linear_factors_odd d hx hz haEven
    exact ((T12_not_even_iff_odd _).mpr hodd.1) hqsub
  exact T59_xz_four_linear_factors_odd_prime_disjoint
    d hx hz hqPrime hq2 ⟨hqsub,hqadd⟩

/--
Symmetric generalized-Fermat reduction for y=z=4 with b even.
-/
theorem T59_yz_four_b_even_generalized_fermat_squared_bases
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    (hbEven : T12Even d.b) :
    ∃ X Y Z : Nat,
      X ^ d.x + Y ^ d.x = 2 * Z ^ d.x := by
  let P := T59_yz_four_b_even_pure_power_packet d hy hz hbEven
  have hbc_lt : d.b < d.c :=
    T21_right_same_exponent_gap d.a_pos d.equation (by simpa [hy, hz])
  have hid :
      (d.c - d.b) ^ 2 + (d.c + d.b) ^ 2 =
        2 * (d.c ^ 2 + d.b ^ 2) :=
    quartic_linear_square_sum (Nat.le_of_lt hbc_lt)
  rw [P.sub_eq, P.add_eq, P.quad_eq] at hid
  refine ⟨P.u^2, P.v^2, P.w, ?_⟩
  simpa [pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hid

#print axioms MCore.T59_xz_four_a_even_generalized_fermat
#print axioms MCore.T59_xz_four_a_even_generalized_fermat_squared_bases
#print axioms MCore.T59_xz_four_a_even_uv_coprime
#print axioms MCore.T59_yz_four_b_even_generalized_fermat_squared_bases

end MCore
