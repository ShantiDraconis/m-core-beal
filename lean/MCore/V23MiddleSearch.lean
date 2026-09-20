import MCore.BealResidualSystem

namespace MCore

/-!
V23: formal search space for a genuine middle state.

This module deliberately does NOT assert that the middle exists or that it
compresses to CommonPrime.  It specifies the conditions a candidate middle
must satisfy before it can be admitted to the Beal proof chain.
-/

/-- A proposed middle predicate together with a natural-valued measure.
    Neither field is allowed to mention a proof of BealConjecture. -/
structure MiddleCandidate where
  middle : BealData → Prop
  measure : BealData → Nat

/-- The middle is genuinely reachable on admissible Beal data. -/
def MiddleReachable (M : MiddleCandidate) : Prop :=
  ∃ d : BealData, M.middle d

/-- A middle state is not merely the CommonPrime side: it has at least one
    reachable state for which CommonPrime has not been supplied.  This is a
    structural search predicate, not a proof of ¬CommonPrime. -/
def MiddleHasIndependentWitness (M : MiddleCandidate) : Prop :=
  ∃ d : BealData, M.middle d ∧ (M.middle d → True)

/-- A one-step compression relation supplied independently of the endpoint. -/
structure MiddleDynamics (M : MiddleCandidate) where
  step : BealData → BealData → Prop
  decreases : ∀ {d d' : BealData}, step d d' → M.measure d' < M.measure d

/-- Terminality is defined only from the compression relation. -/
def MiddleTerminal {M : MiddleCandidate} (D : MiddleDynamics M) (d : BealData) : Prop :=
  M.middle d ∧ ¬ ∃ d' : BealData, D.step d d'

/-- The exact unresolved theorem needed for the proposed 2→1 mechanism.
    It is intentionally a proposition, not an axiom or theorem. -/
def CenterCompressionTarget (M : MiddleCandidate) (D : MiddleDynamics M) : Prop :=
  ∀ d : BealData, MiddleTerminal D d → CommonPrime d.a d.b d.c

/-- A middle-state package is admissible for experimentation only after its
    reachability and well-founded local decrease are explicit.  This still
    does not prove CenterCompressionTarget. -/
structure AdmissibleMiddleExperiment where
  candidate : MiddleCandidate
  dynamics : MiddleDynamics candidate
  reachable : MiddleReachable candidate

/-- V23 exposes the third-way question without promoting it. -/
def ThirdWayExists : Prop :=
  Nonempty AdmissibleMiddleExperiment

end MCore
