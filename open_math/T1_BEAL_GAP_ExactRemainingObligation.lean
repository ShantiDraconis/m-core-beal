import MCore.BealEffectiveKernel

namespace MCore.OpenMath

/--
T1-BEAL terminal OPEN_MATH.
This is definitionally the frozen scalar GCD lower-bound producer.
No inhabitant is asserted here.
-/
abbrev T1_BEAL_GAP : Prop :=
  MCore.BealEffective.ExactRemainingObligation

#check MCore.BealEffective.exact_remaining_iff_gcdLowerBoundProducer
#check MCore.BealEffective.exact_remaining_closes_beal
#check MCore.BealEffective.gcd3_eq_one_of_not_lowerBound

end MCore.OpenMath
