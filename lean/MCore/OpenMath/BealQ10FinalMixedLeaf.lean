import MCore.OpenMath.BealQ10ExternalFLT

namespace MCore.OpenMath.BealQ10

/--
Terminal OPEN_MATH leaf for Beal after all frozen structural reductions and
the diagonal/equal-exponent families are discharged.

This is deliberately opaque at the orchestration layer: downstream code must
either construct this proposition materially or leave OPEN_MATH open.  It must
not decompose it into fresh wrappers that merely restate the same five mixed
families.
-/
def FinalMixedExclusion : Prop :=
  FiveMixedFamilyMinCut

/-- A material producer for the one terminal leaf closes Q10 immediately. -/
theorem finalMixedExclusion_closes_Q10
    (h : FinalMixedExclusion) :
    MCore.OpenMath.BealProbe.MaterialPrimitiveExclusion := by
  exact fiveMixedFamilyMinCut_closes_Q10 h

/--
Exact terminal producer type.  There is no default inhabitant and no axiom,
sorry, admit, or hypothetical endpoint hidden here.
-/
def FinalMixedProducer : Type :=
  { h : FinalMixedExclusion // True }

theorem finalMixedProducer_closes_Q10
    (P : FinalMixedProducer) :
    MCore.OpenMath.BealProbe.MaterialPrimitiveExclusion :=
  finalMixedExclusion_closes_Q10 P.1

#print axioms MCore.OpenMath.BealQ10.finalMixedExclusion_closes_Q10
#print axioms MCore.OpenMath.BealQ10.finalMixedProducer_closes_Q10

end MCore.OpenMath.BealQ10
