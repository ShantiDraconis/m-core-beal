import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem prime_pow_dvd_left_of_not_dvd_right
    {q A B k : Nat}
    (hq : IsPrime q)
    (hqB : ¬ q ∣ B)
    (h : q ^ k ∣ A * B) :
    q ^ k ∣ A := by
  induction k generalizing A with
  | zero =>
      simp
  | succ k ih =>
      have hqAB : q ∣ A * B := by
        rcases h with ⟨t, ht⟩
        refine ⟨q ^ k * t, ?_⟩
        rw [ht, Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hqA : q ∣ A := by
        rcases prime_dvd_mul_local hq hqAB with hA | hB
        · exact hA
        · exact False.elim (hqB hB)
      rcases hqA with ⟨A1, hA⟩
      rcases h with ⟨t, ht⟩
      have hcancel : A1 * B = q ^ k * t := by
        have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq.1
        apply Nat.eq_of_mul_eq_mul_left hqpos
        calc
          q * (A1 * B) = (q * A1) * B := by simp [Nat.mul_assoc]
          _ = A * B := by rw [← hA]
          _ = q ^ (k + 1) * t := ht
          _ = q * (q ^ k * t) := by
                rw [Nat.pow_succ]
                simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hkA1 : q ^ k ∣ A1 :=
        ih hq hqB ⟨t, hcancel⟩
      rcases hkA1 with ⟨s, hs⟩
      refine ⟨s, ?_⟩
      rw [hA, hs, Nat.pow_succ]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem gcd_one_for_divisor_left
    {A A1 B : Nat}
    (hA1 : A1 ∣ A)
    (hAB : Nat.gcd A B = 1) :
    Nat.gcd A1 B = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro d hdA1 hdB
  have hdA : d ∣ A := nat_dvd_trans hdA1 hA1
  have hdG : d ∣ Nat.gcd A B := Nat.dvd_gcd hdA hdB
  rw [hAB] at hdG
  have hle : d ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hdG
  omega

private theorem pow_factor_cancel
    {q b b1 p : Nat}
    (hb : b = q * b1) :
    b ^ p = q ^ p * b1 ^ p := by
  rw [hb, Nat.mul_pow]

/--
Standalone statement of the core UFD step.  It intentionally duplicates only
the proposition shape, not any Beal-specific conclusion.
-/
def CoprimePairPrimePowerSplittingCore : Prop :=
  ∀ A B b p : Nat,
    OddPrimeExponent p →
    Nat.gcd A B = 1 →
    b ^ p = A * B →
    ∃ u v : Nat, A = u ^ p ∧ B = v ^ p

/--
Core proof of the UFD step needed by the quartic Beal branch.
No Nat.factorization and no Mathlib are used.
-/
theorem coprimePairPrimePowerSplitting_core :
    CoprimePairPrimePowerSplittingCore := by
  intro A
  induction A using Nat.lt_wfRel.wf.induction with
  | h A ih =>
      intro B b p hp hAB hpow
      by_cases hA0 : A = 0
      · subst A
        have hB1 : B = 1 := by
          simpa using hAB
        have hb0 : b = 0 := by
          have hpPos : 0 < p := Nat.lt_trans (by decide : 0 < 2) hp.2
          by_contra hbne
          have hbPos : 0 < b := Nat.pos_of_ne_zero hbne
          have hpowPos : 0 < b ^ p := Nat.pow_pos hbPos
          rw [hpow] at hpowPos
          simp at hpowPos
        refine ⟨0, 1, ?_, ?_⟩
        · subst b
          have hp0 : p ≠ 0 := Nat.ne_of_gt (Nat.lt_trans (by decide : 0 < 2) hp.2)
          simp [hp0]
        · simpa [hB1]
      by_cases hA1 : A = 1
      · subst A
        have hBpow : B = b ^ p := by
          simpa using hpow.symm
        exact ⟨1, b, by simp, hBpow⟩
      have hAgt : 1 < A := by
        have hApos : 0 < A := Nat.pos_of_ne_zero hA0
        omega
      rcases primeDivisorProperty_proved A hAgt with ⟨q, hq, hqA⟩
      have hqB : ¬ q ∣ B := by
        intro hdivB
        have hdivG : q ∣ Nat.gcd A B := Nat.dvd_gcd hqA hdivB
        rw [hAB] at hdivG
        have hle : q ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hdivG
        exact (Nat.not_le_of_gt hq.1) hle
      have hqBpow : q ∣ b ^ p := by
        rw [hpow]
        rcases hqA with ⟨k, hk⟩
        refine ⟨k * B, ?_⟩
        rw [hk]
        simp [Nat.mul_assoc]
      have hqb : q ∣ b := prime_dvd_pow_reflect hq hqBpow
      rcases hqb with ⟨b1, hb⟩
      have hqp_bpow : q ^ p ∣ b ^ p := by
        refine ⟨b1 ^ p, ?_⟩
        exact pow_factor_cancel hb
      have hqp_AB : q ^ p ∣ A * B := by
        rw [← hpow]
        exact hqp_bpow
      have hqp_A : q ^ p ∣ A :=
        prime_pow_dvd_left_of_not_dvd_right hq hqB hqp_AB
      rcases hqp_A with ⟨A1, hAeq⟩
      have hqppos : 0 < q ^ p := by
        have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq.1
        exact Nat.pow_pos hqpos
      have hA1lt : A1 < A := by
        have hqpgt : 1 < q ^ p := by
          have hpPos : 0 < p := Nat.lt_trans (by decide : 0 < 2) hp.2
          have hqq : q ∣ q := ⟨1, (Nat.mul_one q).symm⟩
          have hqpow : q ∣ q ^ p := dvd_pow_of_dvd hpPos hqq
          have hqle : q ≤ q ^ p :=
            Nat.le_of_dvd (Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one hq.1)) hqpow
          exact Nat.lt_of_lt_of_le hq.1 hqle
        have hA1pos : 0 < A1 := by
          by_contra hzero
          have : A1 = 0 := Nat.eq_zero_of_not_pos hzero
          rw [this] at hAeq
          simp at hAeq
          exact hA0 hAeq
        rw [hAeq]
        have hlt :
            1 * A1 < (q ^ p) * A1 :=
          Nat.mul_lt_mul_of_pos_right hqpgt hA1pos
        simpa using hlt
      have hA1dvdA : A1 ∣ A := by
        refine ⟨q ^ p, ?_⟩
        rw [hAeq, Nat.mul_comm]
      have hA1B : Nat.gcd A1 B = 1 :=
        gcd_one_for_divisor_left hA1dvdA hAB
      have hbpow : b ^ p = q ^ p * b1 ^ p :=
        pow_factor_cancel hb
      have hcancel : b1 ^ p = A1 * B := by
        apply Nat.eq_of_mul_eq_mul_left hqppos
        calc
          q ^ p * b1 ^ p = b ^ p := hbpow.symm
          _ = A * B := hpow
          _ = (q ^ p * A1) * B := by rw [hAeq]
          _ = q ^ p * (A1 * B) := by rw [Nat.mul_assoc]
      rcases ih A1 hA1lt B b1 p hp hA1B hcancel with
        ⟨u, v, hA1pow, hBpow⟩
      refine ⟨q * u, v, ?_, hBpow⟩
      calc
        A = q ^ p * A1 := hAeq
        _ = q ^ p * u ^ p := by rw [hA1pow]
        _ = (q * u) ^ p := by rw [Nat.mul_pow]

#print axioms MCore.BealEffective.OpenMath.coprimePairPrimePowerSplitting_core

end OpenMath
end BealEffective
end MCore
