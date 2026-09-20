import MCore.K10

namespace MCore

/-- V0 residue: starting from the actual Beal data (including the
    Diophantine equation and exponents > 2), produce a nontrivial
    common divisor of a, b, and c. -/
def V0EquationToCommonDivisor : Prop :=
  ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c

/-- T0: any Beal proof implies the V0 divisor residue. -/
theorem T0_beal_to_v0
    (h : BealConjecture) : V0EquationToCommonDivisor := by
  intro d
  exact (commonPrime_iff_commonDivisor).mp (h d)

/-- T1 / V1 backward closure: once V0 is discharged, K10 converts the
    nontrivial common divisor into a common prime, closing Beal. -/
theorem T1_v0_to_beal
    (h : V0EquationToCommonDivisor) : BealConjecture := by
  intro d
  exact (commonPrime_iff_commonDivisor).mpr (h d)

/-- V2 collision: after K10, the Beal endpoint is exactly equivalent to V0.
    This isolates the remaining mathematical bridge without promoting it. -/
theorem T2_v2_collision :
    BealConjecture ↔ V0EquationToCommonDivisor :=
  ⟨T0_beal_to_v0, T1_v0_to_beal⟩

/-- T3 sharpens V0 by removing the BealData wrapper.  This is the raw
    Diophantine bridge that remains to be proved. -/
def T3RawEquationDivisorBridge : Prop :=
  ∀ a b c x y z : Nat,
    0 < a → 0 < b → 0 < c →
    2 < x → 2 < y → 2 < z →
    a ^ x + b ^ y = c ^ z →
    ∃ q : Nat, CommonDivisor q a b c

theorem T3_v0_iff_raw :
    V0EquationToCommonDivisor ↔ T3RawEquationDivisorBridge := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz heq
    let d : BealData :=
      { a := a
        b := b
        c := c
        x := x
        y := y
        z := z
        a_pos := ha
        b_pos := hb
        c_pos := hc
        x_gt_two := hx
        y_gt_two := hy
        z_gt_two := hz
        equation := heq }
    exact h d
  · intro h d
    exact h d.a d.b d.c d.x d.y d.z
      d.a_pos d.b_pos d.c_pos d.x_gt_two d.y_gt_two d.z_gt_two d.equation

/-- T4 is the constructive obstruction direction: if T3 holds, there is no
    admissible equation with no nontrivial common divisor. -/
def T4NoPrimitiveEquation : Prop :=
  ∀ a b c x y z : Nat,
    0 < a → 0 < b → 0 < c →
    2 < x → 2 < y → 2 < z →
    (¬ ∃ q : Nat, CommonDivisor q a b c) →
    a ^ x + b ^ y ≠ c ^ z

theorem T4_from_T3
    (h : T3RawEquationDivisorBridge) : T4NoPrimitiveEquation := by
  intro a b c x y z ha hb hc hx hy hz hNo heq
  exact hNo (h a b c x y z ha hb hc hx hy hz heq)

theorem T3_closes_beal
    (h : T3RawEquationDivisorBridge) : BealConjecture :=
  T1_v0_to_beal ((T3_v0_iff_raw).mpr h)

#print axioms MCore.T0_beal_to_v0
#print axioms MCore.T1_v0_to_beal
#print axioms MCore.T2_v2_collision
#print axioms MCore.T3_v0_iff_raw
#print axioms MCore.T4_from_T3
#print axioms MCore.T3_closes_beal

end MCore
