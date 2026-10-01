import MCore.BealQuarticParityPowerForms

namespace MCore

/--
On x=z=4 with a the unique even base, the quadratic factor c^2+a^2 is odd.
-/
theorem T59_xz_four_a_even_quadratic_factor_odd
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    T12Odd (d.c ^ 2 + d.a ^ 2) := by
  have hcOdd : T12Odd d.c := by
    rcases d.exactlyOneEven with hA | hB | hC
    · exact (T12_not_even_iff_odd d.c).mp hA.2.2
    · exact False.elim (hB.1 haEven)
    · exact False.elim (hC.1 haEven)
  have haMod : d.a % 2 = 0 := Nat.mod_eq_zero_of_dvd haEven
  have hcMod : d.c % 2 = 1 := hcOdd
  unfold T12Odd
  rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod, haMod, hcMod]
  norm_num

/--
Therefore all three quartic factors are exact y-th powers on this orientation.
-/
structure T59XZFourAEvenPurePowerPacket
    (d : T59ResidualCandidate) : Prop where
  hx : d.x = 4
  hz : d.z = 4
  haEven : T12Even d.a
  u : Nat
  v : Nat
  w : Nat
  sub_eq : d.c - d.a = u ^ d.y
  add_eq : d.c + d.a = v ^ d.y
  quad_eq : d.c ^ 2 + d.a ^ 2 = w ^ d.y

def T59_xz_four_a_even_pure_power_packet
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    T59XZFourAEvenPurePowerPacket d := by
  rcases T59_xz_four_a_even_linear_factors_are_powers d hx hz haEven with
    ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  have hqOdd := T59_xz_four_a_even_quadratic_factor_odd d hx hz haEven
  have hq2 : (d.c ^ 2 + d.a ^ 2).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    exact (T12_not_even_iff_odd _).mpr hqOdd
  rcases (T59_xz_four_full_power_forms d hx hz).quad_form with ⟨w, hw⟩
  refine {
    hx := hx
    hz := hz
    haEven := haEven
    u := u
    v := v
    w := w
    sub_eq := hu
    add_eq := hv
    quad_eq := ?_
  }
  simpa [hq2] using hw

/--
The product factorization then identifies b^y with (u*v*w)^y.
-/
theorem T59_xz_four_a_even_product_power_identity
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    ∃ u v w : Nat,
      d.c - d.a = u ^ d.y ∧
      d.c + d.a = v ^ d.y ∧
      d.c ^ 2 + d.a ^ 2 = w ^ d.y ∧
      d.b ^ d.y = (u * v * w) ^ d.y := by
  let P := T59_xz_four_a_even_pure_power_packet d hx hz haEven
  refine ⟨P.u, P.v, P.w, P.sub_eq, P.add_eq, P.quad_eq, ?_⟩
  have hfac := T59_xz_four_exact_factorization d hx hz
  rw [P.sub_eq, P.add_eq, P.quad_eq] at hfac
  simpa [mul_pow, Nat.mul_assoc] using hfac

/--
Because y>0, natural-number power injectivity yields the concrete base identity
b = u*v*w.
-/
theorem T59_xz_four_a_even_base_product
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    ∃ u v w : Nat,
      d.c - d.a = u ^ d.y ∧
      d.c + d.a = v ^ d.y ∧
      d.c ^ 2 + d.a ^ 2 = w ^ d.y ∧
      d.b = u * v * w := by
  rcases T59_xz_four_a_even_product_power_identity d hx hz haEven with
    ⟨u,v,w,hsub,hadd,hquad,hpow⟩
  have hyPos : 0 < d.y :=
    Nat.lt_trans (by decide : 0 < 2) d.y_reduced.1
  have hbase : d.b = u * v * w :=
    (Nat.pow_left_injective hyPos).mp hpow
  exact ⟨u,v,w,hsub,hadd,hquad,hbase⟩

/--
Symmetric pure-power packet for y=z=4 with b the unique even base.
-/
structure T59YZFourBEvenPurePowerPacket
    (d : T59ResidualCandidate) : Prop where
  hy : d.y = 4
  hz : d.z = 4
  hbEven : T12Even d.b
  u : Nat
  v : Nat
  w : Nat
  sub_eq : d.c - d.b = u ^ d.x
  add_eq : d.c + d.b = v ^ d.x
  quad_eq : d.c ^ 2 + d.b ^ 2 = w ^ d.x

def T59_yz_four_b_even_pure_power_packet
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    (hbEven : T12Even d.b) :
    T59YZFourBEvenPurePowerPacket d := by
  rcases T59_yz_four_b_even_linear_factors_are_powers d hy hz hbEven with
    ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  have hcOdd : T12Odd d.c := by
    rcases d.exactlyOneEven with hA | hB | hC
    · exact False.elim (hA.2.1 hbEven)
    · exact (T12_not_even_iff_odd d.c).mp hB.2.2
    · exact False.elim (hC.2.1 hbEven)
  have hbMod : d.b % 2 = 0 := Nat.mod_eq_zero_of_dvd hbEven
  have hcMod : d.c % 2 = 1 := hcOdd
  have hqOdd : T12Odd (d.c ^ 2 + d.b ^ 2) := by
    unfold T12Odd
    rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod, hbMod, hcMod]
    norm_num
  have hq2 : (d.c ^ 2 + d.b ^ 2).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    exact (T12_not_even_iff_odd _).mpr hqOdd
  rcases (T59_yz_four_full_power_forms d hy hz).quad_form with ⟨w, hw⟩
  refine {
    hy := hy
    hz := hz
    hbEven := hbEven
    u := u
    v := v
    w := w
    sub_eq := hu
    add_eq := hv
    quad_eq := ?_
  }
  simpa [hq2] using hw

theorem T59_yz_four_b_even_base_product
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    (hbEven : T12Even d.b) :
    ∃ u v w : Nat,
      d.c - d.b = u ^ d.x ∧
      d.c + d.b = v ^ d.x ∧
      d.c ^ 2 + d.b ^ 2 = w ^ d.x ∧
      d.a = u * v * w := by
  let P := T59_yz_four_b_even_pure_power_packet d hy hz hbEven
  have hfac := T59_yz_four_exact_factorization d hy hz
  rw [P.sub_eq, P.add_eq, P.quad_eq] at hfac
  have hpow : d.a ^ d.x = (P.u * P.v * P.w) ^ d.x := by
    simpa [mul_pow, Nat.mul_assoc] using hfac
  have hxPos : 0 < d.x :=
    Nat.lt_trans (by decide : 0 < 2) d.x_reduced.1
  have hbase : d.a = P.u * P.v * P.w :=
    (Nat.pow_left_injective hxPos).mp hpow
  exact ⟨P.u,P.v,P.w,P.sub_eq,P.add_eq,P.quad_eq,hbase⟩

#print axioms MCore.T59_xz_four_a_even_pure_power_packet
#print axioms MCore.T59_xz_four_a_even_base_product
#print axioms MCore.T59_yz_four_b_even_pure_power_packet
#print axioms MCore.T59_yz_four_b_even_base_product

end MCore
