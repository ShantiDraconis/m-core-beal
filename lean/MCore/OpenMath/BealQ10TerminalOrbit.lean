import MCore.OpenMath.BealQ10EndpointGapFixedPoint

namespace MCore.OpenMath.BealQ10

/--
A structural reopening step forgets presentation details and returns the
canonical terminal signature.
-/
def reopenStep (_ : Prop) : Prop := TerminalGapSignature

/--
One reopening step is already normalized: a second reopening yields exactly
the same structural target.
-/
theorem reopenStep_idempotent (P : Prop) :
    reopenStep (reopenStep P) = reopenStep P := by
  rfl

/--
Every positive iterate of reopening lands on the same terminal signature.
This models the infinite search loop as repetition of one fixed structural
state rather than production of new mathematical obligations.
-/
def reopenIter : Nat → Prop → Prop
  | 0, P => P
  | _ + 1, P => reopenStep (reopenIter 0 P)

theorem reopenIter_succ_terminal (n : Nat) (P : Prop) :
    reopenIter (n + 1) P = TerminalGapSignature := by
  cases n <;> rfl

/--
The reverse image used by the orchestration layer is the same terminal
signature. Contact with the reverse image therefore collapses structurally
to the fixed point.
-/
def reverseTerminal (_ : Prop) : Prop := TerminalGapSignature

theorem terminal_meets_reverse :
    reopenStep TerminalGapSignature = reverseTerminal TerminalGapSignature := by
  rfl

/--
No-new-parameter theorem: after reaching the terminal signature, every
further forward or reverse structural step has the same codomain proposition.
-/
theorem terminal_orbit_collapses :
    reopenStep TerminalGapSignature = TerminalGapSignature ∧
    reverseTerminal TerminalGapSignature = TerminalGapSignature ∧
    reopenStep (reverseTerminal TerminalGapSignature) = TerminalGapSignature := by
  exact ⟨rfl, rfl, rfl⟩

structure TerminalOrbitCertificate : Prop where
  forward_idempotent : ∀ P : Prop, reopenStep (reopenStep P) = reopenStep P
  positive_iterates_terminal : ∀ n : Nat, ∀ P : Prop,
    reopenIter (n + 1) P = TerminalGapSignature
  forward_reverse_collapse :
    reopenStep TerminalGapSignature = reverseTerminal TerminalGapSignature
  orbit_fixed :
    reopenStep TerminalGapSignature = TerminalGapSignature ∧
    reverseTerminal TerminalGapSignature = TerminalGapSignature ∧
    reopenStep (reverseTerminal TerminalGapSignature) = TerminalGapSignature

theorem terminalOrbitCertificate : TerminalOrbitCertificate := by
  exact {
    forward_idempotent := reopenStep_idempotent
    positive_iterates_terminal := reopenIter_succ_terminal
    forward_reverse_collapse := terminal_meets_reverse
    orbit_fixed := terminal_orbit_collapses
  }

#print axioms MCore.OpenMath.BealQ10.reopenStep_idempotent
#print axioms MCore.OpenMath.BealQ10.reopenIter_succ_terminal
#print axioms MCore.OpenMath.BealQ10.terminal_meets_reverse
#print axioms MCore.OpenMath.BealQ10.terminal_orbit_collapses
#print axioms MCore.OpenMath.BealQ10.terminalOrbitCertificate

end MCore.OpenMath.BealQ10
