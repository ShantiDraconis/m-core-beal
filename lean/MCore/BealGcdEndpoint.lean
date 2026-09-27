import MCore.BealCommonDivisorEndpoint

namespace MCore

/-- Triple gcd encoded by iterated Nat.gcd. -/
def BealTripleGCD (d : BealData) : Nat :=
  Nat.gcd (Nat.gcd d.a d.b) d.c

/-- The gcd endpoint: every admissible Beal datum has nontrivial triple gcd. -/
def BealGcdEndpoint : Prop :=
  ∀ d : BealData, 1 < BealTripleGCD d

/-- A nontrivial triple gcd directly gives a nontrivial common divisor. -/
theorem gcdEndpoint_to_commonDivisorEndpoint
    (h : BealGcdEndpoint) : BealCommonDivisorEndpoint := by
  intro d
  refine ⟨BealTripleGCD d, h d, ?_, ?_, ?_⟩
  · exact dvd_trans (Nat.gcd_dvd_left d.a d.b) (Nat.gcd_dvd_left (Nat.gcd d.a d.b) d.c)
  · exact dvd_trans (Nat.gcd_dvd_right d.a d.b) (Nat.gcd_dvd_left (Nat.gcd d.a d.b) d.c)
  · exact Nat.gcd_dvd_right (Nat.gcd d.a d.b) d.c

/-- Therefore the gcd endpoint closes Beal through the already certified chain. -/
theorem gcdEndpoint_closes_beal
    (h : BealGcdEndpoint) : BealConjecture :=
  commonDivisorEndpoint_closes_beal (gcdEndpoint_to_commonDivisorEndpoint h)

/-- Certificate object for the gcd formulation. -/
structure BealUniversalGcdCertificate where
  witness : BealGcdEndpoint

def universalGcd_to_commonDivisorCertificate
    (C : BealUniversalGcdCertificate) :
    BealUniversalCommonDivisorCertificate :=
  ⟨gcdEndpoint_to_commonDivisorEndpoint C.witness⟩

def universalGcd_to_finalRoot
    (C : BealUniversalGcdCertificate) :
    BealFinalRoot :=
  universalCommonDivisor_to_finalRoot
    (universalGcd_to_commonDivisorCertificate C)

#print axioms MCore.gcdEndpoint_to_commonDivisorEndpoint
#print axioms MCore.gcdEndpoint_closes_beal
#print axioms MCore.universalGcd_to_commonDivisorCertificate
#print axioms MCore.universalGcd_to_finalRoot

end MCore
