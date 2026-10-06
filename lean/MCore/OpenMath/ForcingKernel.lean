import MCore.BealSpecification
import MCore.BackwardAudit.WithoutOracle
import MCore.OpenMath.P02RejectionBealInvariantProbe

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
