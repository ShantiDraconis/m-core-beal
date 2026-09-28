import MCore.BealSpecification

namespace MCore.BealMaterialProbe

/-
EXPECTED FAILURE TARGET.
No CommonPrimeWitnessContract or endpoint-equivalent hypothesis is supplied.
-/

example : ∀ d : BealData, CommonPrime d.a d.b d.c := by

end MCore.BealMaterialProbe
