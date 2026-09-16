import MCore.K7

namespace MCore

/-- Exact negation of the Beal endpoint for one admissible datum. -/
def NoCommonPrime (d : BealData) : Prop :=
  ¬ CommonPrime d.a d.b d.c

/-- A datum satisfying `NoCommonPrime` is precisely a counterexample candidate. -/
theorem noCommonPrime_is_counterexample (d : BealData) :
    NoCommonPrime d ↔ BealCounterexample d := by
  rfl

/-- Beal is equivalent to saying that no admissible datum has the endpoint obstruction. -/
theorem beal_iff_no_counterexample :
    BealConjecture ↔ ∀ d : BealData, ¬ BealCounterexample d := by
  constructor
  · intro h d hd
    exact hd (h d)
  · intro h d
    by_contra hd
    exact h d hd

/-- A proof eliminating `NoCommonPrime` for every admissible datum closes the endpoint. -/
theorem closeBeal_from_noCommonPrime_elimination
    (h : ∀ d : BealData, ¬ NoCommonPrime d) : BealConjecture := by
  intro d
  by_contra hd
  exact h d hd

end MCore
