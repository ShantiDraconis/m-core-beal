import MCore.K10
import MCore.BealSpecification

namespace MCore.BealMaterialProbe

/-
EXPECTED FAILURE TARGET.
No CommonPrimeWitnessContract, CommonPrime hypothesis, or endpoint-equivalent
oracle is supplied.
-/

example : ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c := by

end MCore.BealMaterialProbe
