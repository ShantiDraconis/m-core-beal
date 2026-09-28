import MCore.BealMinimalProducer

namespace MCore

/-- Authoritative reduced material target for Beal.
    K10 proves this is equivalent to BealConjecture, but no inhabitant is
    supplied here. -/
def MinimalBealInhabitant : Prop :=
  CommonDivisorProducer

end MCore
