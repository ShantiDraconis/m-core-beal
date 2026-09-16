import MCore.K9

namespace MCore

/-- K10 candidate: constructive proof that every natural number greater than one
    has a divisor satisfying the repository-local `IsPrime` predicate.

    The proof uses strong induction on `n`. If `n` is already prime, choose it.
    Otherwise the negation of `IsPrime n` supplies a proper nontrivial divisor;
    strong induction yields a prime divisor of that divisor, and K9 divisibility
    transitivity lifts it to a prime divisor of `n`.
-/
theorem primeDivisorProperty_core : PrimeDivisorProperty := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hp : IsPrime n
      · exact ⟨n, hp, ⟨1, by simp⟩⟩
      · have hnotall : ¬ (∀ d : Nat, d ∣ n → d = 1 ∨ d = n) := by
          intro hall
          exact hp ⟨hn, hall⟩
        push_neg at hnotall
        obtain ⟨d, hdn, hd1, hdn_eq⟩ := hnotall
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
          have hk1 : 1 ≤ k := hkpos
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
