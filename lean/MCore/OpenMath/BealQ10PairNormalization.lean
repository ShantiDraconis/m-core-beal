import MCore.OpenMath.BealQ10Core012Dynamics

namespace MCore.OpenMath.BealQ10

/-- Two-coordinate terminal code used to express the user's normalization laws. -/
structure CorePair where
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def normalize01 : CorePair := ⟨1, 1⟩
def normalize02 : CorePair := ⟨2, 2⟩

theorem zero_one_tends_one_one :
    (CorePair.mk 0 1) ≠ normalize01 ∧
    normalize01 = CorePair.mk 1 1 := by
  exact ⟨by decide, rfl⟩

theorem zero_two_tends_two_two :
    (CorePair.mk 0 2) ≠ normalize02 ∧
    normalize02 = CorePair.mk 2 2 := by
  exact ⟨by decide, rfl⟩

/-- Deterministic normalization matching the two terminal transition rules. -/
def normalizePair : CorePair → CorePair
  | ⟨0, 1⟩ => ⟨1, 1⟩
  | ⟨0, 2⟩ => ⟨2, 2⟩
  | p => p

theorem normalizePair_01 :
    normalizePair ⟨0, 1⟩ = ⟨1, 1⟩ := by
  rfl

theorem normalizePair_02 :
    normalizePair ⟨0, 2⟩ = ⟨2, 2⟩ := by
  rfl

theorem normalizePair_11_fixed :
    normalizePair ⟨1, 1⟩ = ⟨1, 1⟩ := by
  rfl

theorem normalizePair_22_fixed :
    normalizePair ⟨2, 2⟩ = ⟨2, 2⟩ := by
  rfl

structure PairNormalizationCertificate : Prop where
  zero_one : normalizePair ⟨0, 1⟩ = ⟨1, 1⟩
  zero_two : normalizePair ⟨0, 2⟩ = ⟨2, 2⟩
  one_fixed : normalizePair ⟨1, 1⟩ = ⟨1, 1⟩
  two_fixed : normalizePair ⟨2, 2⟩ = ⟨2, 2⟩

theorem pairNormalizationCertificate : PairNormalizationCertificate := by
  exact {
    zero_one := normalizePair_01
    zero_two := normalizePair_02
    one_fixed := normalizePair_11_fixed
    two_fixed := normalizePair_22_fixed
  }

#print axioms MCore.OpenMath.BealQ10.pairNormalizationCertificate

end MCore.OpenMath.BealQ10
