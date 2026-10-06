import MCore.OpenMath.BealQ10TerminalInhabitantBehavior

namespace MCore.OpenMath.BealQ10

abbrev Endpoint : Prop := FinalRoot
abbrev Gap : Prop := Endpoint
abbrev Habitant : Prop := Gap
abbrev Inhabitant : Prop := Habitant

theorem endpoint_to_gap : Endpoint → Gap := id
theorem gap_to_habitant : Gap → Habitant := id
theorem habitant_to_inhabitant : Habitant → Inhabitant := id
theorem inhabitant_to_endpoint : Inhabitant → Endpoint := id

theorem endpoint_gap_iff : Endpoint ↔ Gap := Iff.rfl
theorem gap_habitant_iff : Gap ↔ Habitant := Iff.rfl
theorem habitant_inhabitant_iff : Habitant ↔ Inhabitant := Iff.rfl
theorem inhabitant_endpoint_iff : Inhabitant ↔ Endpoint := Iff.rfl

theorem terminal_cycle :
    (Endpoint ↔ Gap) ∧
    (Gap ↔ Habitant) ∧
    (Habitant ↔ Inhabitant) ∧
    (Inhabitant ↔ Endpoint) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/--
The cycle is logically closed, but this theorem makes the existence question
explicit: an inhabitant of any node is exactly an inhabitant of Endpoint.
-/
theorem cycle_inhabited_iff_endpoint :
    Nonempty Endpoint ↔ Nonempty Inhabitant := by
  constructor
  · intro h
    rcases h with ⟨e⟩
    exact ⟨e⟩
  · intro h
    rcases h with ⟨i⟩
    exact ⟨i⟩

/--
Kernel-facing no-extra-premise formulation: any proof that the terminal cycle
alone yields Endpoint must supply an actual Endpoint term.
-/
def TerminalCycleClosed : Prop :=
  terminal_cycle.1 ∧ terminal_cycle.2.1 ∧ terminal_cycle.2.2.1 ∧ terminal_cycle.2.2.2

theorem terminalCycleClosed : TerminalCycleClosed := by
  exact ⟨endpoint_gap_iff, gap_habitant_iff, habitant_inhabitant_iff, inhabitant_endpoint_iff⟩

#print axioms MCore.OpenMath.BealQ10.terminal_cycle
#print axioms MCore.OpenMath.BealQ10.cycle_inhabited_iff_endpoint
#print axioms MCore.OpenMath.BealQ10.terminalCycleClosed

end MCore.OpenMath.BealQ10
