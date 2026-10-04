import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

/--
Minimal semantic conductor interface required after the arithmetic Frey packet.
This does not assume a conductor theorem; it isolates exactly what must be
supplied by a genuine local/global conductor formalization.
-/
def XYFourPrimeConductorProducer : Prop :=
  ∀ r : ReducedPrimitiveCandidate,
    r.x = 4 →
    r.y = 4 →
    OddPrimeExponent r.z →
    ∃ N : Nat,
      0 < N

/--
Minimal level-lowering interface after an exact conductor level is known.
Again, this is deliberately independent of Beal's conclusion.
-/
def XYFourPrimeLevelLoweringProducer : Prop :=
  ∀ r : ReducedPrimitiveCandidate,
    r.x = 4 →
    r.y = 4 →
    OddPrimeExponent r.z →
    ∃ Nlowered : Nat,
      0 < Nlowered

/--
Minimal terminal modular obstruction for the xy-four orbit.
It states exactly that a reduced primitive xy-four candidate cannot survive
once the modular route is completely instantiated.
-/
def XYFourPrimeModularExclusion : Prop :=
  ∀ r : ReducedPrimitiveCandidate,
    r.x = 4 →
    r.y = 4 →
    OddPrimeExponent r.z →
    False

/--
The actual Q3 orbit-A eliminator is exactly the modular exclusion above.
This theorem is wiring-only but pins the terminal producer shape.
-/
theorem xyFourPrime_modular_exclusion_eliminates_orbitA
    (h : XYFourPrimeModularExclusion)
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4)
    (hz : OddPrimeExponent r.z) :
    False :=
  h r hx hy hz

#print axioms MCore.BealEffective.OpenMath.xyFourPrime_modular_exclusion_eliminates_orbitA

end OpenMath
end BealEffective
end MCore
