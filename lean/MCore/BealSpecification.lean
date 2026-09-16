namespace MCore

/-- Positive-integer data for the Beal equation, represented in `Nat` with positivity explicit. -/
structure BealData where
  A B C : Nat
  x y z : Nat
  A_pos : 0 < A
  B_pos : 0 < B
  C_pos : 0 < C
  x_gt_two : 2 < x
  y_gt_two : 2 < y
  z_gt_two : 2 < z
  equation : A ^ x + B ^ y = C ^ z

/-- A natural number is a nontrivial common divisor of the three bases. -/
def CommonDivisor (d A B C : Nat) : Prop :=
  1 < d ∧ d ∣ A ∧ d ∣ B ∧ d ∣ C

/-- Prime-witness formulation used by the official Beal statement. -/
def CommonPrime (A B C : Nat) : Prop :=
  ∃ p : Nat, Nat.Prime p ∧ p ∣ A ∧ p ∣ B ∧ p ∣ C

/-- The exact unresolved mathematical endpoint. This is a definition, not a theorem. -/
def BealConjecture : Prop :=
  ∀ d : BealData, CommonPrime d.A d.B d.C

/-- A counterexample is exactly admissible Beal data with no common-prime witness. -/
def BealCounterexample (d : BealData) : Prop :=
  ¬ CommonPrime d.A d.B d.C

/-- Pure logic: a counterexample refutes the conjecture. -/
theorem counterexample_refutes (d : BealData) (h : BealCounterexample d) : ¬ BealConjecture := by
  intro hBeal
  exact h (hBeal d)

/-- Pure logic: Beal excludes every represented counterexample. -/
theorem conjecture_excludes_counterexamples (h : BealConjecture) (d : BealData) :
    ¬ BealCounterexample d := by
  intro hd
  exact hd (h d)

end MCore
