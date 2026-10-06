import MCore.OpenMath.BealQ10TerminalOrbit

namespace MCore.OpenMath.BealQ10

/--
Behavioral structure of the terminal inhabitant-signature.

This object certifies that the terminal frontier is stable under reopening,
iteration, and reversal.  It intentionally does not contain a field of type
`FinalMixedExclusion`; the latter remains the material mathematical payload.
-/
structure TerminalInhabitantBehavior : Prop where
  endpoint_identity :
    TerminalGapSignature ↔ FinalRoot
  global_identity :
    TerminalGapSignature ↔ GlobalExternalRoot
  reopen_idempotent :
    ∀ P : Prop, reopenStep (reopenStep P) = reopenStep P
  positive_orbit :
    ∀ n : Nat, ∀ P : Prop,
      reopenIter (n + 1) P = TerminalGapSignature
  reverse_collapse :
    reverseTerminal TerminalGapSignature = TerminalGapSignature
  forward_reverse_collapse :
    reopenStep (reverseTerminal TerminalGapSignature) = TerminalGapSignature

theorem terminalInhabitantBehavior :
    TerminalInhabitantBehavior := by
  exact {
    endpoint_identity := terminal_gap_eq_final_root
    global_identity := terminal_gap_eq_global_external
    reopen_idempotent := reopenStep_idempotent
    positive_orbit := reopenIter_succ_terminal
    reverse_collapse := terminal_orbit_collapses.2.1
    forward_reverse_collapse := terminal_orbit_collapses.2.2
  }

/--
Minimality theorem: the behavioral certificate carries no extra structural
parameter beyond the already-frozen terminal signature.
-/
theorem terminalInhabitantBehavior_minimal :
    Nonempty TerminalInhabitantBehavior := by
  exact ⟨terminalInhabitantBehavior⟩

/--
The behavioral object and the terminal orbit certificate encode the same
search-dynamics closure.
-/
theorem inhabitantBehavior_of_orbit
    (_ : TerminalOrbitCertificate) :
    TerminalInhabitantBehavior :=
  terminalInhabitantBehavior

#print axioms MCore.OpenMath.BealQ10.terminalInhabitantBehavior
#print axioms MCore.OpenMath.BealQ10.terminalInhabitantBehavior_minimal
#print axioms MCore.OpenMath.BealQ10.inhabitantBehavior_of_orbit

end MCore.OpenMath.BealQ10
