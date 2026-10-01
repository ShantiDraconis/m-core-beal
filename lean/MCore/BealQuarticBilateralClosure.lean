import MCore.BealQuarticValuationPacket
import MCore.BealTwoSidedResolution

namespace MCore

/--
Positive-side quartic contradiction producer.

This does NOT assume Beal.  It says that every fully reduced T59 residual
candidate is impossible once its unconditional quartic arithmetic packet is
taken into account.
-/
structure QuarticResidualContradictionProducer : Prop where
  eliminate :
    ∀ d : T59ResidualCandidate,
      False

/-- Any such producer closes Beal positively because T59 is the exact residual
counterexample class. -/
theorem quarticResidualContradictionProducer_closes_beal
    (h : QuarticResidualContradictionProducer) :
    BealConjecture := by
  apply bealConjecture_iff_gcdLowerBoundProducer.mpr
  intro d
  exfalso
  exact h.eliminate d

/--
Negative-side producer remains one concrete residual candidate.
-/
abbrev QuarticResidualCounterexampleProducer := T59ResidualCandidate

/--
Bilateral quartic resolution object.  Neither side stores Beal as an input.
-/
def BealQuarticBilateralResolved : Prop :=
  Nonempty QuarticResidualContradictionProducer ∨
  Nonempty QuarticResidualCounterexampleProducer

theorem beal_quartic_bilateral_outcome
    (h : BealQuarticBilateralResolved) :
    BealConjecture ∨ ¬ BealConjecture := by
  rcases h with hp | hn
  · rcases hp with ⟨p⟩
    exact Or.inl (quarticResidualContradictionProducer_closes_beal p)
  · rcases hn with ⟨d⟩
    exact Or.inr d.refutesBeal

theorem beal_quartic_both_routes_contradict
    (hp : Nonempty QuarticResidualContradictionProducer)
    (hn : Nonempty QuarticResidualCounterexampleProducer) :
    False := by
  rcases hp with ⟨p⟩
  rcases hn with ⟨d⟩
  exact d.refutesBeal
    (quarticResidualContradictionProducer_closes_beal p)

/--
Every residual candidate automatically carries the complete unconditional
quartic valuation packet proved so far. This makes the next positive attack
strictly smaller: eliminate candidates satisfying these already-proved laws.
-/
theorem every_T59_has_quartic_valuation_packet
    (d : T59ResidualCandidate) :
    T59QuarticValuationPacket d :=
  T59_quartic_valuation_packet d

#print axioms MCore.quarticResidualContradictionProducer_closes_beal
#print axioms MCore.beal_quartic_bilateral_outcome
#print axioms MCore.beal_quartic_both_routes_contradict
#print axioms MCore.every_T59_has_quartic_valuation_packet

end MCore
