import MCore.OpenMath.BealQ10TerminalFixedPoint

namespace MCore.OpenMath.BealQ10

/--
The terminal gap is not a new structural object: by construction it is the
same proposition already designated as the final mathematical root.
-/
def TerminalGapSignature : Prop := FinalMixedExclusion

theorem terminal_gap_eq_final_root :
    TerminalGapSignature ↔ FinalRoot := by
  rfl

theorem terminal_gap_eq_terminal_signature :
    TerminalGapSignature ↔ TerminalSignature := by
  rfl

theorem terminal_gap_eq_global_external :
    TerminalGapSignature ↔ GlobalExternalRoot := by
  rfl

/--
Reopening the terminal gap at the orchestration layer yields no new logical
payload: the reopened target is definitionally the same terminal signature.
-/
def reopenTerminal (_ : TerminalGapSignature) : Prop := TerminalGapSignature

theorem reopenTerminal_no_new_information
    (h : TerminalGapSignature) :
    reopenTerminal h ↔ TerminalGapSignature := by
  rfl

/--
Certificate that endpoint, gap and published root are one structural
fixed-point signature. This is a termination certificate for decomposition,
not an inhabitant of the terminal proposition.
-/
structure EndpointGapFixedPointCertificate : Prop where
  gap_root : TerminalGapSignature ↔ FinalRoot
  gap_terminal : TerminalGapSignature ↔ TerminalSignature
  gap_global : TerminalGapSignature ↔ GlobalExternalRoot
  reopen_fixed :
    ∀ h : TerminalGapSignature,
      reopenTerminal h ↔ TerminalGapSignature

theorem endpointGapFixedPointCertificate :
    EndpointGapFixedPointCertificate := by
  exact {
    gap_root := terminal_gap_eq_final_root
    gap_terminal := terminal_gap_eq_terminal_signature
    gap_global := terminal_gap_eq_global_external
    reopen_fixed := reopenTerminal_no_new_information
  }

#print axioms MCore.OpenMath.BealQ10.terminal_gap_eq_final_root
#print axioms MCore.OpenMath.BealQ10.terminal_gap_eq_terminal_signature
#print axioms MCore.OpenMath.BealQ10.terminal_gap_eq_global_external
#print axioms MCore.OpenMath.BealQ10.reopenTerminal_no_new_information
#print axioms MCore.OpenMath.BealQ10.endpointGapFixedPointCertificate

end MCore.OpenMath.BealQ10
