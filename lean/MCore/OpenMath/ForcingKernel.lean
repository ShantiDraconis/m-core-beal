import MCore.BealSpecification
import MCore.BackwardAudit.WithoutOracle
import MCore.OpenMath.P02RejectionBealInvariantProbe
import MCore.OpenMath.BealQ10PrimitiveExclusion
import MCore.OpenMath.BealQ10Parity
import MCore.OpenMath.BealQ10FLT4
import MCore.OpenMath.BealQ10SevenFamilies
import MCore.OpenMath.BealQ10SixFamilyMinCut
import MCore.OpenMath.BealQ10PrimitiveReduced
import MCore.OpenMath.BealQ10ExternalFLT
import MCore.OpenMath.BealQ10FinalMixedLeaf
import MCore.OpenMath.BealQ10FinalRoot
import MCore.OpenMath.BealQ10TerminalFixedPoint
import MCore.OpenMath.BealQ10EndpointGapFixedPoint
import MCore.OpenMath.BealQ10TerminalOrbit
import MCore.OpenMath.BealQ10TerminalInhabitantBehavior
import MCore.OpenMath.BealQ10TerminalCycle
import MCore.OpenMath.BealQ10Core012Dynamics
import MCore.OpenMath.BealQ10PairNormalization
import MCore.OpenMath.BealQ10FinalPolarity
import MCore.OpenMath.BealQ10FinalReflexivity
import MCore.OpenMath.BealQ10TerminalClosureTransition
import MCore.OpenMath.BealQ10RPAFiveView
import MCore.OpenMath.BealQ10ExponentReduction

namespace MCore.OpenMath.Beal

def FirstRealOpenMath : Prop :=
  ∀ d : MCore.BealData, MCore.CommonPrime d.a d.b d.c

theorem first_real_open_math_iff_beal :
    FirstRealOpenMath ↔ MCore.BealConjecture := by
  rfl

theorem close_from_first_real_open_math
    (h : FirstRealOpenMath) : MCore.BealConjecture := h

#print axioms MCore.OpenMath.Beal.close_from_first_real_open_math

end MCore.OpenMath.Beal
