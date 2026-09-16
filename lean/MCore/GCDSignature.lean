import MCore.BealSpecification

namespace MCore

/-- Any common-prime witness is automatically a nontrivial common divisor. -/
theorem commonPrime_to_commonDivisor {A B C : Nat} (h : CommonPrime A B C) :
    ∃ d : Nat, CommonDivisor d A B C := by
  rcases h with ⟨p, hp, hpA, hpB, hpC⟩
  exact ⟨p, hp.one_lt, hpA, hpB, hpC⟩

/-- A common prime divides the nested gcd. -/
theorem commonPrime_dvd_gcd {A B C : Nat} (h : CommonPrime A B C) :
    ∃ p : Nat, Nat.Prime p ∧ p ∣ Nat.gcd A (Nat.gcd B C) := by
  rcases h with ⟨p, hp, hpA, hpB, hpC⟩
  have hpBC : p ∣ Nat.gcd B C := (Nat.dvd_gcd_iff).2 ⟨hpB, hpC⟩
  have hpABC : p ∣ Nat.gcd A (Nat.gcd B C) := (Nat.dvd_gcd_iff).2 ⟨hpA, hpBC⟩
  exact ⟨p, hp, hpABC⟩

/-- A common prime forces the three-way gcd to be nontrivial. -/
theorem commonPrime_gcd_ne_one {A B C : Nat} (h : CommonPrime A B C) :
    Nat.gcd A (Nat.gcd B C) ≠ 1 := by
  rcases commonPrime_dvd_gcd h with ⟨p, hp, hpd⟩
  intro hg
  rw [hg] at hpd
  exact hp.not_dvd_one hpd

/-- If the nested gcd is one, there cannot be a common prime. -/
theorem gcd_one_no_commonPrime {A B C : Nat}
    (h : Nat.gcd A (Nat.gcd B C) = 1) : ¬ CommonPrime A B C := by
  intro hp
  exact commonPrime_gcd_ne_one hp h

end MCore
