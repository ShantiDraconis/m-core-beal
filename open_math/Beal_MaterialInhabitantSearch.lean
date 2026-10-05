import MCore.BealEffective.ReducedFamilies
import Mathlib

namespace MCore
namespace BealEffective
namespace OpenMath

/-
Deliberately failing material search harness.
No sorry/admit/axiom.  The build is expected to succeed only if automation and
the imported theorem base can actually synthesize the exact material min-cut.
-/

def FLTAt (n : Nat) : Prop :=
  ∀ a b c : Nat,
    0 < a →
    0 < b →
    0 < c →
    a ^ n + b ^ n = c ^ n →
    False

def AllFourEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, AllFour r.x r.y r.z → False
def EqualOddPrimeEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, EqualOddPrime r.x r.y r.z → False
def TwoFourPrimeEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, TwoFourPrime r.x r.y r.z → False
def OneFourEqualPrimesEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, OneFourEqualPrimes r.x r.y r.z → False
def OneFourDistinctPrimesEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, OneFourDistinctPrimes r.x r.y r.z → False
def TwoEqualOddPrimesEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, TwoEqualOddPrimes r.x r.y r.z → False
def ThreeDistinctOddPrimesEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, ThreeDistinctOddPrimes r.x r.y r.z → False

structure MixedFamilyEliminator : Prop where
  twoFourPrime : TwoFourPrimeEliminated
  oneFourEqualPrimes : OneFourEqualPrimesEliminated
  oneFourDistinctPrimes : OneFourDistinctPrimesEliminated
  twoEqualOddPrimes : TwoEqualOddPrimesEliminated
  threeDistinctOddPrimes : ThreeDistinctOddPrimesEliminated

structure ReducedFamilyMinCut : Prop where
  flt4 : FLTAt 4
  primeFLT : ∀ p : Nat, OddPrimeExponent p → FLTAt p
  mixed : MixedFamilyEliminator

/-- Search for the exact positive inhabitant.  Failure is informative. -/
example : ReducedFamilyMinCut := by
  aesop

/-- Search for a concrete reduced counterexample to the terminal lower bound. -/
example : ∃ r : ReducedPrimitiveCandidate, True := by
  aesop

end OpenMath
end BealEffective
end MCore
