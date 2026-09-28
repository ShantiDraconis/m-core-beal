import MCore.BealSpecification

namespace MCore.BealMaterialProbe

/-
EXPECTED FAILURE TARGET.

A material Beal producer must prove CommonPrime for an arbitrary BealData
directly from the Diophantine hypotheses. No CommonPrimeWitnessContract or
endpoint-equivalent hypothesis may be supplied.
-/

def MaterialTarget : Prop :=
  ∀ d : BealData, CommonPrime d.a d.b d.c

end MCore.BealMaterialProbe
