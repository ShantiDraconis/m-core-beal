import MCore.BealSpecification

namespace MCore

theorem commonPrime_to_commonDivisor {a b c : Nat} (h : CommonPrime a b c) :
    ∃ d : Nat, CommonDivisor d a b c := by
  rcases h with ⟨p, hp, hpa, hpb, hpc⟩
  exact ⟨p, hp.1, hpa, hpb, hpc⟩

/-- Exact implication needed by the endpoint: a common-prime witness supplies a nontrivial common divisor. -/
theorem beal_commonPrime_implies_commonDivisor (d : BealData)
    (h : CommonPrime d.a d.b d.c) : ∃ q : Nat, CommonDivisor q d.a d.b d.c :=
  commonPrime_to_commonDivisor h


/-- On the positive Beal domain, having a nontrivial common divisor is exactly
the scalar inequality `1 < gcd(a, gcd(b,c))`.  Positivity is essential:
without it the all-zero triple would make every natural divide all entries while
the gcd is zero. -/
theorem commonDivisor_iff_one_lt_nestedGCD (d : BealData) :
    (∃ q : Nat, CommonDivisor q d.a d.b d.c) ↔
      1 < Nat.gcd d.a (Nat.gcd d.b d.c) := by
  constructor
  · rintro ⟨q, hq, hqa, hqb, hqc⟩
    have hqbc : q ∣ Nat.gcd d.b d.c := Nat.dvd_gcd hqb hqc
    have hqg : q ∣ Nat.gcd d.a (Nat.gcd d.b d.c) :=
      Nat.dvd_gcd hqa hqbc
    have hgpos : 0 < Nat.gcd d.a (Nat.gcd d.b d.c) :=
      Nat.gcd_pos_of_pos_left _ d.a_pos
    exact lt_of_lt_of_le hq (Nat.le_of_dvd hgpos hqg)
  · intro hg
    let g := Nat.gcd d.a (Nat.gcd d.b d.c)
    refine ⟨g, hg, Nat.gcd_dvd_left _ _, ?_, ?_⟩
    · exact (Nat.gcd_dvd_right d.a (Nat.gcd d.b d.c)).trans
        (Nat.gcd_dvd_left d.b d.c)
    · exact (Nat.gcd_dvd_right d.a (Nat.gcd d.b d.c)).trans
        (Nat.gcd_dvd_right d.b d.c)

/-- Consequently the common-prime endpoint itself has the same scalar
characterization on every Beal datum. -/
theorem commonPrime_iff_one_lt_nestedGCD (d : BealData) :
    CommonPrime d.a d.b d.c ↔
      1 < Nat.gcd d.a (Nat.gcd d.b d.c) := by
  rw [commonPrime_iff_commonDivisor, commonDivisor_iff_one_lt_nestedGCD]

end MCore
