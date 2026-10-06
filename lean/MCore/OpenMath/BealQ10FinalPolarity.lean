import MCore.OpenMath.BealQ10PairNormalization
import MCore.OpenMath.BealQ10TerminalCycle

namespace MCore.OpenMath.BealQ10

/-- Structural labels only. OPEN_MATH is the terminal proposition itself. -/
abbrev OpenMath : Prop := Endpoint

/-- A proposition is materially closed only when the endpoint is inhabited. -/
def ClosedMath : Prop := Endpoint

theorem openMath_iff_closedMath :
    OpenMath ↔ ClosedMath := by
  rfl

/--
If one additionally asserts ClosedMath ↔ ¬ OpenMath while OpenMath and
ClosedMath are definitionally the same proposition, the system collapses
to Endpoint ↔ ¬ Endpoint.
-/
theorem closedMath_iff_notOpenMath_iff_endpoint_self_negation :
    (ClosedMath ↔ ¬ OpenMath) ↔ (Endpoint ↔ ¬ Endpoint) := by
  rfl

/--
No proposition can be equivalent to its own negation in Lean's logic.
-/
theorem not_endpoint_iff_not_endpoint :
    ¬ (Endpoint ↔ ¬ Endpoint) := by
  intro h
  by_cases e : Endpoint
  · exact (h.mp e) e
  · have e' : Endpoint := h.mpr e
    exact e e'

theorem not_closedMath_iff_notOpenMath :
    ¬ (ClosedMath ↔ ¬ OpenMath) := by
  intro h
  exact not_endpoint_iff_not_endpoint
    (closedMath_iff_notOpenMath_iff_endpoint_self_negation.mp h)

/--
The only consistent structural identity among the user's final equations is
OpenMath ↔ ClosedMath when both names denote the same terminal proposition.
The negated identity is refuted.
-/
structure FinalPolarityCertificate : Prop where
  same_signature : OpenMath ↔ ClosedMath
  self_negation_impossible : ¬ (ClosedMath ↔ ¬ OpenMath)

theorem finalPolarityCertificate : FinalPolarityCertificate := by
  exact {
    same_signature := openMath_iff_closedMath
    self_negation_impossible := not_closedMath_iff_notOpenMath
  }

#print axioms MCore.OpenMath.BealQ10.openMath_iff_closedMath
#print axioms MCore.OpenMath.BealQ10.not_endpoint_iff_not_endpoint
#print axioms MCore.OpenMath.BealQ10.not_closedMath_iff_notOpenMath
#print axioms MCore.OpenMath.BealQ10.finalPolarityCertificate

end MCore.OpenMath.BealQ10
