import MCore.BealSpecification
import MCore.V5.BealPayload

namespace MCore.V5

/-- Exact mathematical residue. This is a proposition definition, not an axiom
    and not a theorem claimed by the V5 structural layer. -/
def ArithmeticResidue : Prop :=
  ∀ d : MCore.BealData, MCore.BealCounterexample d → False

theorem beal_of_arithmetic_residue (h : ArithmeticResidue) :
    MCore.BealConjecture := by
  intro d
  by_contra hn
  exact h d hn

/-- Dependency marker only: V5 does not inhabit this proposition. -/
def FinalProofRequires : Prop := ArithmeticResidue

end MCore.V5
