import MCore.OpenMath.BealQ10FinalPolarity

namespace MCore.OpenMath.BealQ10

/-- Self-inequality of a well-defined proposition is impossible by reflexivity. -/
theorem not_openMath_ne_self :
    ¬ (OpenMath ≠ OpenMath) := by
  intro h
  exact h rfl

theorem not_closedMath_ne_self :
    ¬ (ClosedMath ≠ ClosedMath) := by
  intro h
  exact h rfl

/--
If either terminal label is required to differ from itself, the resulting
system is inconsistent.
-/
theorem self_inequality_collapses
    (hO : OpenMath ≠ OpenMath) :
    False := by
  exact hO rfl

theorem closed_self_inequality_collapses
    (hC : ClosedMath ≠ ClosedMath) :
    False := by
  exact hC rfl

structure FinalReflexivityCertificate : Prop where
  open_reflexive : OpenMath = OpenMath
  closed_reflexive : ClosedMath = ClosedMath
  open_self_neq_impossible : ¬ (OpenMath ≠ OpenMath)
  closed_self_neq_impossible : ¬ (ClosedMath ≠ ClosedMath)

theorem finalReflexivityCertificate :
    FinalReflexivityCertificate := by
  exact {
    open_reflexive := rfl
    closed_reflexive := rfl
    open_self_neq_impossible := not_openMath_ne_self
    closed_self_neq_impossible := not_closedMath_ne_self
  }

#print axioms MCore.OpenMath.BealQ10.not_openMath_ne_self
#print axioms MCore.OpenMath.BealQ10.not_closedMath_ne_self
#print axioms MCore.OpenMath.BealQ10.finalReflexivityCertificate

end MCore.OpenMath.BealQ10
