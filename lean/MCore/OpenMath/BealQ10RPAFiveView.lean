import MCore.OpenMath.BealQ10TerminalClosureTransition

namespace MCore.OpenMath.BealQ10

/-- RPA bridge views: all are the same terminal proposition seen through
different certification layers. -/
abbrev OpenBridge : Prop := OpenMath
abbrev ClosedBridge : Prop := ClosedMath
abbrev MathRoot : Prop := Endpoint
abbrev FinalRootView : Prop := FinalRoot
abbrev GlobalExternalCertificate : Prop := GlobalExternalRoot

theorem openMath_iff_openBridge :
    OpenMath ↔ OpenBridge := Iff.rfl

theorem closedMath_iff_closedBridge :
    ClosedMath ↔ ClosedBridge := Iff.rfl

theorem openBridge_iff_mathRoot :
    OpenBridge ↔ MathRoot := Iff.rfl

theorem closedBridge_iff_mathRoot :
    ClosedBridge ↔ MathRoot := Iff.rfl

theorem mathRoot_iff_finalRoot :
    MathRoot ↔ FinalRootView := Iff.rfl

theorem finalRoot_iff_globalExternalCertificate :
    FinalRootView ↔ GlobalExternalCertificate := Iff.rfl

/--
The RPA confirmation object contains both sides of the transition at once,
plus the identity-preserving forward/backward maps.
-/
structure RPADualConfirmation : Prop where
  openWitness : OpenMath
  closedWitness : ClosedMath
  forward : OpenMath → ClosedMath
  backward : ClosedMath → OpenMath
  preserve_forward : forward openWitness = closedWitness
  preserve_backward : backward closedWitness = openWitness

/--
Any endpoint witness canonically induces the complete dual confirmation.
-/
theorem endpoint_to_rpaDualConfirmation
    (h : Endpoint) :
    RPADualConfirmation := by
  exact {
    openWitness := h
    closedWitness := h
    forward := openMath_to_closedMath
    backward := closedMath_to_openMath
    preserve_forward := rfl
    preserve_backward := rfl
  }

/--
Conversely, an RPA dual confirmation contains the endpoint witness. Thus the
confirmation is neither weaker nor stronger than the terminal mathematical
payload: it is the same inhabitant viewed as a certified transition.
-/
theorem rpaDualConfirmation_to_endpoint
    (R : RPADualConfirmation) :
    Endpoint :=
  R.openWitness

theorem rpaDualConfirmation_iff_endpoint :
    Nonempty RPADualConfirmation ↔ Nonempty Endpoint := by
  constructor
  · rintro ⟨R⟩
    exact ⟨rpaDualConfirmation_to_endpoint R⟩
  · rintro ⟨h⟩
    exact ⟨endpoint_to_rpaDualConfirmation h⟩

/--
Five-view identity:
OPEN/CLOSED transition = bridge transition = MATH = FINAL_ROOT =
GLOBAL_EXTERNAL_CERTIFICATE.
-/
structure RPAFiveViewCertificate : Prop where
  open_bridge : OpenMath ↔ OpenBridge
  closed_bridge : ClosedMath ↔ ClosedBridge
  open_math : OpenBridge ↔ MathRoot
  closed_math : ClosedBridge ↔ MathRoot
  final_root : MathRoot ↔ FinalRootView
  global_external : FinalRootView ↔ GlobalExternalCertificate

theorem rpaFiveViewCertificate :
    RPAFiveViewCertificate := by
  exact {
    open_bridge := openMath_iff_openBridge
    closed_bridge := closedMath_iff_closedBridge
    open_math := openBridge_iff_mathRoot
    closed_math := closedBridge_iff_mathRoot
    final_root := mathRoot_iff_finalRoot
    global_external := finalRoot_iff_globalExternalCertificate
  }

#print axioms MCore.OpenMath.BealQ10.rpaFiveViewCertificate
#print axioms MCore.OpenMath.BealQ10.rpaDualConfirmation_iff_endpoint
#print axioms MCore.OpenMath.BealQ10.endpoint_to_rpaDualConfirmation
#print axioms MCore.OpenMath.BealQ10.rpaDualConfirmation_to_endpoint

end MCore.OpenMath.BealQ10
