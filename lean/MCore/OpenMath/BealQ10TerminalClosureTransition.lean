import MCore.OpenMath.BealQ10FinalReflexivity

namespace MCore.OpenMath.BealQ10

/-- The terminal transition requested by the user. Since OpenMath and
ClosedMath are aliases of the same terminal proposition, the transition is
definitionally the identity map. -/
theorem openMath_to_closedMath :
    OpenMath → ClosedMath := id

theorem closedMath_to_openMath :
    ClosedMath → OpenMath := id

theorem open_closed_equiv :
    OpenMath ↔ ClosedMath := by
  exact ⟨openMath_to_closedMath, closedMath_to_openMath⟩

/-- A named transition relation for publication. -/
def TerminalClosureTransition : Prop :=
  OpenMath → ClosedMath

theorem terminalClosureTransition :
    TerminalClosureTransition := by
  exact openMath_to_closedMath

/-- No information is created by applying the closure transition twice. -/
theorem terminalClosure_idempotent
    (h : OpenMath) :
    openMath_to_closedMath h = h := by
  rfl

structure TerminalClosureCertificate : Prop where
  forward : OpenMath → ClosedMath
  backward : ClosedMath → OpenMath
  equivalence : OpenMath ↔ ClosedMath
  idempotent : ∀ h : OpenMath, openMath_to_closedMath h = h

theorem terminalClosureCertificate :
    TerminalClosureCertificate := by
  exact {
    forward := openMath_to_closedMath
    backward := closedMath_to_openMath
    equivalence := open_closed_equiv
    idempotent := terminalClosure_idempotent
  }

#print axioms MCore.OpenMath.BealQ10.openMath_to_closedMath
#print axioms MCore.OpenMath.BealQ10.closedMath_to_openMath
#print axioms MCore.OpenMath.BealQ10.terminalClosureTransition
#print axioms MCore.OpenMath.BealQ10.terminalClosureCertificate

end MCore.OpenMath.BealQ10
