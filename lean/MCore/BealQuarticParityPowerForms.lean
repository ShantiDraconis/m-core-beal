import MCore.BealQuarticFullPowerForms

namespace MCore

/--
If a is the unique even base on x=z=4, then c-a and c+a are odd.
-/
theorem T59_xz_four_a_even_linear_factors_odd
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    T12Odd (d.c - d.a) ∧ T12Odd (d.c + d.a) := by
  have hcOdd : T12Odd d.c := by
    rcases d.exactlyOneEven with hA | hB | hC
    · exact (T12_not_even_iff_odd d.c).mp hA.2.2
    · exact False.elim (hB.1 haEven)
    · exact False.elim (hC.1 haEven)
  have haMod : d.a % 2 = 0 := Nat.mod_eq_zero_of_dvd haEven
  have hcMod : d.c % 2 = 1 := hcOdd
  constructor
  · unfold T12Odd
    rw [Nat.sub_mod]
    omega
  · unfold T12Odd
    rw [Nat.add_mod, haMod, hcMod]
    norm_num

/--
Hence the two linear factors have zero 2-adic multiplicity.
-/
theorem T59_xz_four_a_even_linear_factorization_two_zero
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    (d.c - d.a).factorization 2 = 0 ∧
    (d.c + d.a).factorization 2 = 0 := by
  rcases T59_xz_four_a_even_linear_factors_odd d hx hz haEven with ⟨hsub, hadd⟩
  constructor
  · apply Nat.factorization_eq_zero_of_not_dvd
    exact (T12_not_even_iff_odd _).mpr hsub
  · apply Nat.factorization_eq_zero_of_not_dvd
    exact (T12_not_even_iff_odd _).mpr hadd

/--
On the a-even orientation of x=z=4, c-a and c+a are exact y-th powers.
-/
theorem T59_xz_four_a_even_linear_factors_are_powers
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    (∃ u : Nat, d.c - d.a = u ^ d.y) ∧
    (∃ v : Nat, d.c + d.a = v ^ d.y) := by
  have forms := T59_xz_four_full_power_forms d hx hz
  have h2 := T59_xz_four_a_even_linear_factorization_two_zero d hx hz haEven
  constructor
  · rcases forms.sub_form with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    simpa [h2.1] using hu
  · rcases forms.add_form with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa [h2.2] using hv

/--
Symmetric result: if b is the unique even base on y=z=4, then c-b and c+b
are exact x-th powers.
-/
theorem T59_yz_four_b_even_linear_factors_are_powers
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    (hbEven : T12Even d.b) :
    (∃ u : Nat, d.c - d.b = u ^ d.x) ∧
    (∃ v : Nat, d.c + d.b = v ^ d.x) := by
  have hcOdd : T12Odd d.c := by
    rcases d.exactlyOneEven with hA | hB | hC
    · exact False.elim (hA.2.1 hbEven)
    · exact (T12_not_even_iff_odd d.c).mp hB.2.2
    · exact False.elim (hC.2.1 hbEven)
  have hbMod : d.b % 2 = 0 := Nat.mod_eq_zero_of_dvd hbEven
  have hcMod : d.c % 2 = 1 := hcOdd
  have hsubOdd : T12Odd (d.c - d.b) := by
    unfold T12Odd
    rw [Nat.sub_mod]
    omega
  have haddOdd : T12Odd (d.c + d.b) := by
    unfold T12Odd
    rw [Nat.add_mod, hbMod, hcMod]
    norm_num
  have hsub2 : (d.c - d.b).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    exact (T12_not_even_iff_odd _).mpr hsubOdd
  have hadd2 : (d.c + d.b).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    exact (T12_not_even_iff_odd _).mpr haddOdd
  have forms := T59_yz_four_full_power_forms d hy hz
  constructor
  · rcases forms.sub_form with ⟨u, hu⟩
    exact ⟨u, by simpa [hsub2] using hu⟩
  · rcases forms.add_form with ⟨v, hv⟩
    exact ⟨v, by simpa [hadd2] using hv⟩

#print axioms MCore.T59_xz_four_a_even_linear_factors_are_powers
#print axioms MCore.T59_yz_four_b_even_linear_factors_are_powers

end MCore
