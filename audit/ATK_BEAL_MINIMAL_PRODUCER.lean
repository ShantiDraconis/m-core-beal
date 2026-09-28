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

#print axioms MCore.bealConjecture_iff_commonDivisorProducer

end MCore
