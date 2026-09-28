import MCore.BealSpecification

namespace MCore

/-- Single authoritative material target for Beal. -/
def MinimalBealInhabitant : Prop :=
  ∀ d : BealData, CommonPrime d.a d.b d.c

end MCore
