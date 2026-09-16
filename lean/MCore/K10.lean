import MCore.K9
import Std.Tactic.Omega

namespace MCore

/-- K10 candidate: every natural number greater than one has a divisor satisfying
    the repository-local `IsPrime` predicate.  This first repair removes the
    unavailable Mathlib-only `push_neg` dependency and isolates any remaining
    trust dependency for the explicit K10 axiom audit. -/
theorem primeDivisorProperty_core : PrimeDivisorProperty := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hp : IsPrime n
      · exact ⟨n, hp, ⟨1, by simp⟩⟩
      · have hnotall : ¬ (∀ d : Nat, d ∣ n → d = 1 ∨ d = n) := by
          intro hall
          exact hp ⟨hn, hall⟩
        have hex : ∃ d : Nat, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
          by_contra hnone
          apply hnotall
          intro d hdn
          by_cases hd1 : d = 1
          · exact Or.inl hd1
          · right
            by_contra hdn'
            exact hnone ⟨d, hdn, hd1, hdn'⟩
        obtain ⟨d, hdn, hd1, hdn_eq⟩ := hex
        have hdpos : 0 < d := by
          by_contra hz
          have hd0 : d = 0 := Nat.eq_zero_of_not_pos hz
          subst d
          rcases hdn with ⟨k, hk⟩
          simp at hk
          omega
        have hdgt1 : 1 < d := by omega
        have hdlt : d < n := by
          rcases hdn with ⟨k, hk⟩
          have hkpos : 0 < k := by
            by_contra hkz
            have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkz
            subst k
            simp at hk
            omega
          have hdle : d ≤ n := by
            rw [hk]
            exact Nat.le_mul_of_pos_right d hkpos
          exact Nat.lt_of_le_of_ne hdle hdn_eq
        obtain ⟨p, hprime, hpd⟩ := ih d hdlt hdgt1
        exact ⟨p, hprime, nat_dvd_trans hpd hdn⟩

/-- K10 discharges the explicit K9 prime-divisor hypothesis. -/
theorem primeDivisorProperty_proved : PrimeDivisorProperty :=
  primeDivisorProperty_core

/-- With the elementary prime-divisor theorem discharged, common-prime and
    nontrivial-common-divisor formulations are unconditionally equivalent. -/
theorem commonPrime_iff_commonDivisor {a b c : Nat} :
    CommonPrime a b c ↔ ∃ d : Nat, CommonDivisor d a b c :=
  commonPrime_iff_commonDivisor_of_primeDivisor primeDivisorProperty_proved

end MCore
