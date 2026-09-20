import MCore.T15

namespace MCore

theorem T16_odd_square_mod_eight
    {a : Nat} (ha : T12Odd a) :
    a ^ 2 % 8 = 1 := by
  have hdecomp := Nat.mod_add_div a 4
  rcases T13_odd_mod_four ha with h1 | h3
  · rw [h1] at hdecomp
    have haform : a = 1 + 4 * (a / 4) := hdecomp.symm
    rw [haform]
    simp [Nat.pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mul_assoc]
  · rw [h3] at hdecomp
    have haform : a = 3 + 4 * (a / 4) := hdecomp.symm
    rw [haform]
    simp [Nat.pow_succ, Nat.mul_mod, Nat.add_mod, Nat.mul_assoc]

theorem T16_odd_fourth_mod_eight
    {a : Nat} (ha : T12Odd a) :
    a ^ 4 % 8 = 1 := by
  have h2 : a ^ 2 % 8 = 1 := T16_odd_square_mod_eight ha
  have h4 : a ^ 4 = (a ^ 2) * (a ^ 2) := by
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [h4, Nat.mul_mod, h2]
  simp

theorem T16_even_pow_mod_eight
    {c z : Nat} (hc : T12Even c) (hz : 2 < z) :
    c ^ z % 8 = 0 := by
  cases z with
  | zero =>
      exact False.elim (Nat.not_lt_zero 2 hz)
  | succ z =>
      cases z with
      | zero =>
          exact False.elim ((Nat.not_lt_of_ge (by decide : 1 ≤ 2)) hz)
      | succ z =>
          cases z with
          | zero =>
              exact False.elim ((Nat.not_lt_of_ge (by decide : 2 ≤ 2)) hz)
          | succ z =>
              have hcc : 4 ∣ c * c := by
                have h22 : 2 * 2 ∣ c * c := Nat.mul_dvd_mul hc hc
                simpa using h22
              have hccc : 8 ∣ (c * c) * c := by
                have h42 : 4 * 2 ∣ (c * c) * c := Nat.mul_dvd_mul hcc hc
                simpa using h42
              have hmul : 8 ∣ c ^ z * ((c * c) * c) :=
                Nat.dvd_mul_left_of_dvd hccc (c ^ z)
              apply Nat.mod_eq_zero_of_dvd
              simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

private theorem T16_mod_eight_succ_zero_forces_seven
    {r : Nat} (hlt : r < 8) (hzero : (1 + r) % 8 = 0) :
    r = 7 := by
  cases r with
  | zero =>
      simp at hzero
  | succ r =>
      cases r with
      | zero =>
          simp at hzero
      | succ r =>
          cases r with
          | zero =>
              simp at hzero
          | succ r =>
              cases r with
              | zero =>
                  simp at hzero
              | succ r =>
                  cases r with
                  | zero =>
                      simp at hzero
                  | succ r =>
                      cases r with
                      | zero =>
                          simp at hzero
                      | succ r =>
                          cases r with
                          | zero =>
                              simp at hzero
                          | succ r =>
                              cases r with
                              | zero =>
                                  rfl
                              | succ r =>
                                  have hge : 8 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ r)))))))) := by
                                    exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le r))))))))
                                  exact False.elim ((Nat.not_le_of_gt hlt) hge)

theorem T16_c_even_left_four_forces_right_seven
    {a b c x y z : Nat}
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hc : T12Even c)
    (hx4 : x = 4) :
    b ^ y % 8 = 7 := by
  have hna : ¬ T12Even a := by
    rcases hpar with ha | hb | hcOnly
    · exact False.elim (ha.2.2 hc)
    · exact hb.1
    · exact hcOnly.1
  have hoa : T12Odd a := (T12_not_even_iff_odd a).mp hna
  subst x
  have ha8 : a ^ 4 % 8 = 1 := T16_odd_fourth_mod_eight hoa
  have hc8 : c ^ z % 8 = 0 := T16_even_pow_mod_eight hc hz.1
  have hmod := congrArg (fun n : Nat => n % 8) heq
  change (a ^ 4 + b ^ y) % 8 = c ^ z % 8 at hmod
  rw [Nat.add_mod, ha8, hc8] at hmod
  have hlt : b ^ y % 8 < 8 := Nat.mod_lt _ (by decide)
  exact T16_mod_eight_succ_zero_forces_seven hlt hmod

theorem T16_c_even_right_four_forces_left_seven
    {a b c x y z : Nat}
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hc : T12Even c)
    (hy4 : y = 4) :
    a ^ x % 8 = 7 := by
  have hnb : ¬ T12Even b := by
    rcases hpar with ha | hb | hcOnly
    · exact ha.2.1
    · exact False.elim (hb.2.2 hc)
    · exact hcOnly.2.1
  have hob : T12Odd b := (T12_not_even_iff_odd b).mp hnb
  subst y
  have hb8 : b ^ 4 % 8 = 1 := T16_odd_fourth_mod_eight hob
  have hc8 : c ^ z % 8 = 0 := T16_even_pow_mod_eight hc hz.1
  have hmod := congrArg (fun n : Nat => n % 8) heq
  change (a ^ x + b ^ 4) % 8 = c ^ z % 8 at hmod
  rw [Nat.add_mod, hb8, hc8] at hmod
  have hlt : a ^ x % 8 < 8 := Nat.mod_lt _ (by decide)
  have hcomm : (1 + a ^ x % 8) % 8 = 0 := by
    simpa [Nat.add_comm] using hmod
  exact T16_mod_eight_succ_zero_forces_seven hlt hcomm

def T16CEightConstraint (a b c x y z : Nat) : Prop :=
  T12Even c →
    (x = 4 → b ^ y % 8 = 7) ∧
    (y = 4 → a ^ x % 8 = 7)

def T16EightReducedCandidate : Prop :=
  ∃ a b c x y z : Nat,
    0 < a ∧
    0 < b ∧
    0 < c ∧
    T7ReducedExponent x ∧
    T7ReducedExponent y ∧
    T7ReducedExponent z ∧
    a ^ x + b ^ y = c ^ z ∧
    T11PairwisePrimitive a b c ∧
    T12ExactlyOneEven a b c ∧
    (T12Even c → ¬ (x = 4 ∧ y = 4)) ∧
    T14CResidueConstraint a b c x y z ∧
    T15CBaseResidueConstraint a b c x y z ∧
    T16CEightConstraint a b c x y z

theorem T16_T15_to_eight :
    T15BaseResidueReducedCandidate → T16EightReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hcpos, hx, hy, hz, heq, hpw, hpar, h44, h14, h15⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hcpos, hx, hy, hz, heq, hpw, hpar, h44, h14, h15, ?_⟩
  intro hce
  constructor
  · intro hx4
    exact T16_c_even_left_four_forces_right_seven hz heq hpar hce hx4
  · intro hy4
    exact T16_c_even_right_four_forces_left_seven hz heq hpar hce hy4

theorem T16_eight_to_T15 :
    T16EightReducedCandidate → T15BaseResidueReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar, h44, h14, h15, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar, h44, h14, h15⟩

theorem T16_candidate_iff_eight :
    T15BaseResidueReducedCandidate ↔ T16EightReducedCandidate :=
  ⟨T16_T15_to_eight, T16_eight_to_T15⟩

def T16EightScientificFrontier : Prop :=
  ¬ T16EightReducedCandidate

theorem T16_beal_iff_eight_frontier :
    BealConjecture ↔ T16EightScientificFrontier := by
  rw [T15_beal_iff_base_residue_frontier]
  unfold T15BaseResidueScientificFrontier T16EightScientificFrontier
  exact not_congr T16_candidate_iff_eight

#print axioms MCore.T16_odd_square_mod_eight
#print axioms MCore.T16_odd_fourth_mod_eight
#print axioms MCore.T16_even_pow_mod_eight
#print axioms MCore.T16_c_even_left_four_forces_right_seven
#print axioms MCore.T16_c_even_right_four_forces_left_seven
#print axioms MCore.T16_candidate_iff_eight
#print axioms MCore.T16_beal_iff_eight_frontier

end MCore
