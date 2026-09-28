import MCore.K10
import MCore.BealSpecification

namespace MCore

/--
Producer compression for Beal.

K10 already proves that a nontrivial common divisor is equivalent to a common
prime divisor. Therefore the terminal producer need not construct the prime
directly. It is enough to construct a nontrivial common divisor for every
admissible Beal datum.

This is a genuine reduction of the producer type; it does not assume the Beal
endpoint.
-/
def CommonDivisorProducer : Prop :=
  ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c

theorem bealConjecture_iff_commonDivisorProducer :
    BealConjecture ↔ CommonDivisorProducer := by
  constructor
  · intro h d
    exact (commonPrime_iff_commonDivisor).mp (h d)
  · intro h d
    exact (commonPrime_iff_commonDivisor).mpr (h d)

/-- Smallest scalar producer currently exposed by the arithmetic kernel. -/
def GCDLowerBoundProducer : Prop :=
  ∀ d : BealData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)

theorem commonDivisorProducer_iff_gcdLowerBoundProducer :
    CommonDivisorProducer ↔ GCDLowerBoundProducer := by
  constructor
  · intro h d
    exact (commonDivisor_iff_one_lt_nestedGCD d).mp (h d)
  · intro h d
    exact (commonDivisor_iff_one_lt_nestedGCD d).mpr (h d)

theorem bealConjecture_iff_gcdLowerBoundProducer :
    BealConjecture ↔ GCDLowerBoundProducer := by
  rw [bealConjecture_iff_commonDivisorProducer,
      commonDivisorProducer_iff_gcdLowerBoundProducer]

#print axioms MCore.commonDivisor_iff_one_lt_nestedGCD
#print axioms MCore.commonPrime_iff_one_lt_nestedGCD
#print axioms MCore.bealConjecture_iff_commonDivisorProducer
#print axioms MCore.bealConjecture_iff_gcdLowerBoundProducer

end MCore
