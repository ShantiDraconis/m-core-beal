import MCore.V5.Surgery

namespace MCore.V5

structure Interpretation (α : Type u) (β : Type v) where
  evalPoint : OmegaPoint α → β
  evalBottom : OmegaBottom α → β

/-- Application-specific soundness obligation; deliberately not an axiom. -/
def SurgerySound (I : Interpretation α β) : Prop :=
  ∀ b, I.evalPoint (S b) = I.evalBottom b

end MCore.V5
