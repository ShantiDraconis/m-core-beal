import MCore.B01DenseScientificFrontier

namespace MCore

/-!
B01 O1 — exact scientific reduction.

The already-certified prefix proves `T60GenuineOddMultiplicativeReduction d`
for every residual candidate.  This file isolates the one genuinely new
mathematical theorem still needed to turn that prefix into the exact odd
local conductor-exponent law.

No conductor semantics are invented here: `S.ActualExponent` remains the
genuine semantics that must be supplied by a verified conductor
formalization.
-/

/-- Genuine local theorem required after the certified multiplicative-
reduction prefix.  It is deliberately stated against the full certified
prefix rather than against a Boolean proxy or an ad-hoc exponent definition. -/
def B01GenuineMultiplicativeConductorTheorem
    (S : B01ConductorExponentSemantics) : Prop :=
  ∀ (d : T59ResidualCandidate),
    T60GenuineOddMultiplicativeReduction d →
    ∀ (p : Nat),
      B01OddBadPrime d p →
      S.ActualExponent d p 1

/-- Exact adapter: once the genuine conductor theorem is supplied, O1 follows
with no additional scientific assumption because the multiplicative-reduction
premise is already GREEN. -/
theorem b01_o1_from_genuine_multiplicative_conductor_theorem
    (S : B01ConductorExponentSemantics)
    (hConductor : B01GenuineMultiplicativeConductorTheorem S) :
    B01OddExponentOneLaw S := by
  intro d p hbad
  exact hConductor d (b01_dense_green_prefix d) p hbad

/-- The irreducible O1 scientific delta after all reusable GREEN work. -/
def B01O1IrreducibleScientificDelta : Type :=
  { S : B01ConductorExponentSemantics //
      B01GenuineMultiplicativeConductorTheorem S }

/-- A real inhabitant of the irreducible delta issues the exact O1
certificate consumed by the atomic B01 DAG. -/
def B01O1IrreducibleScientificDelta.toCertificate
    (H : B01O1IrreducibleScientificDelta) :
    B01O1Certificate where
  semantics := H.1
  law := b01_o1_from_genuine_multiplicative_conductor_theorem H.1 H.2

#print axioms MCore.b01_o1_from_genuine_multiplicative_conductor_theorem

end MCore
