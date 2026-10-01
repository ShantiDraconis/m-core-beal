import MCore.BealQuarticOddPartPowers

namespace MCore

/--
Exact 2-adic times perfect-power reconstruction.
If the odd part of n is an exact e-th power, then n has the form

  n = 2^(v_2(n)) * m^e.

No open hypothesis is involved.
-/
theorem eq_twoPow_mul_pow_of_oddPart_pow
    {n e m : Nat}
    (hodd : Nat.ordCompl 2 n = m ^ e) :
    n = 2 ^ n.factorization 2 * m ^ e := by
  have hdecomp := Nat.ordProj_mul_ordCompl_eq_self n 2
  simpa [hodd] using hdecomp.symm

/--
Full x=z=4 block forms.
-/
structure T59XZFourFullPowerForms
    (d : T59ResidualCandidate) : Prop where
  hx : d.x = 4
  hz : d.z = 4
  sub_form :
    ∃ u : Nat,
      d.c - d.a =
        2 ^ (d.c - d.a).factorization 2 * u ^ d.y
  add_form :
    ∃ v : Nat,
      d.c + d.a =
        2 ^ (d.c + d.a).factorization 2 * v ^ d.y
  quad_form :
    ∃ w : Nat,
      d.c ^ 2 + d.a ^ 2 =
        2 ^ (d.c ^ 2 + d.a ^ 2).factorization 2 * w ^ d.y

def T59_xz_four_full_power_forms
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4) :
    T59XZFourFullPowerForms d := by
  refine {
    hx := hx
    hz := hz
    sub_form := ?_
    add_form := ?_
    quad_form := ?_
  }
  · rcases T59_xz_four_oddPart_sub_is_power d hx hz with ⟨u, hu⟩
    exact ⟨u, eq_twoPow_mul_pow_of_oddPart_pow hu⟩
  · rcases T59_xz_four_oddPart_add_is_power d hx hz with ⟨v, hv⟩
    exact ⟨v, eq_twoPow_mul_pow_of_oddPart_pow hv⟩
  · rcases T59_xz_four_oddPart_quad_is_power d hx hz with ⟨w, hw⟩
    exact ⟨w, eq_twoPow_mul_pow_of_oddPart_pow hw⟩

/--
Full y=z=4 block forms.
-/
structure T59YZFourFullPowerForms
    (d : T59ResidualCandidate) : Prop where
  hy : d.y = 4
  hz : d.z = 4
  sub_form :
    ∃ u : Nat,
      d.c - d.b =
        2 ^ (d.c - d.b).factorization 2 * u ^ d.x
  add_form :
    ∃ v : Nat,
      d.c + d.b =
        2 ^ (d.c + d.b).factorization 2 * v ^ d.x
  quad_form :
    ∃ w : Nat,
      d.c ^ 2 + d.b ^ 2 =
        2 ^ (d.c ^ 2 + d.b ^ 2).factorization 2 * w ^ d.x

def T59_yz_four_full_power_forms
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4) :
    T59YZFourFullPowerForms d := by
  refine {
    hy := hy
    hz := hz
    sub_form := ?_
    add_form := ?_
    quad_form := ?_
  }
  · rcases T59_yz_four_oddPart_sub_is_power d hy hz with ⟨u, hu⟩
    exact ⟨u, eq_twoPow_mul_pow_of_oddPart_pow hu⟩
  · rcases T59_yz_four_oddPart_add_is_power d hy hz with ⟨v, hv⟩
    exact ⟨v, eq_twoPow_mul_pow_of_oddPart_pow hv⟩
  · rcases T59_yz_four_oddPart_quad_is_power d hy hz with ⟨w, hw⟩
    exact ⟨w, eq_twoPow_mul_pow_of_oddPart_pow hw⟩

/--
Every quartic residual branch therefore carries explicit 2-adic times
perfect-power forms, not merely valuation constraints.
-/
structure T59QuarticFullPowerPacket
    (d : T59ResidualCandidate) : Prop where
  xz :
    d.x = 4 -> d.z = 4 -> T59XZFourFullPowerForms d
  yz :
    d.y = 4 -> d.z = 4 -> T59YZFourFullPowerForms d

def T59_quartic_full_power_packet
    (d : T59ResidualCandidate) :
    T59QuarticFullPowerPacket d where
  xz := fun hx hz => T59_xz_four_full_power_forms d hx hz
  yz := fun hy hz => T59_yz_four_full_power_forms d hy hz

#print axioms MCore.eq_twoPow_mul_pow_of_oddPart_pow
#print axioms MCore.T59_xz_four_full_power_forms
#print axioms MCore.T59_yz_four_full_power_forms
#print axioms MCore.T59_quartic_full_power_packet

end MCore
