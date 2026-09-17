import MCore.K9

namespace MCore

/-- K10 candidate: every natural number greater than one has a divisor satisfying
    the repository-local `IsPrime` predicate.  The proof intentionally stays in
    the pinned Lean core environment: no Mathlib-only tactics or imports. -/
theorem primeDivisorProperty_core : PrimeDivisorProperty := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hp : IsPrime n
      · exact ⟨n, hp, ⟨1, rfl⟩⟩
      · have hnotall : ¬ (∀ d : Nat, d ∣ n → d = 1 ∨ d = n) := by
          intro hall
          exact hp ⟨hn, hall⟩
        have hex : ∃ d : Nat, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
          apply Classical.byContradiction
          intro hnone
          apply hnotall
          intro d hdn
          by_cases hd1 : d = 1
          · exact Or.inl hd1
          · right
            apply Classical.byContradiction
            intro hdn'
            exact hnone ⟨d, hdn, hd1, hdn'⟩
        obtain ⟨d, hdn, hd1, hdn_eq⟩ := hex
        have hnpos : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
        have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
        have hdpos : 0 < d := by
          apply Nat.pos_of_ne_zero
          intro hd0
          rcases hdn with ⟨k, hk⟩
          subst d
          exact hn0 (Eq.trans hk rfl)
        have hdgt1 : 1 < d := by
          have hle : 1 ≤ d := Nat.succ_le_of_lt hdpos
          exact Nat.lt_of_le_of_ne hle (Ne.symm hd1)
        have hdlt : d < n := by
          rcases hdn with ⟨k, hk⟩
          have hkpos : 0 < k := by
            apply Nat.pos_of_ne_zero
            intro hk0
            subst k
            exact hn0 (Eq.trans hk rfl)
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
