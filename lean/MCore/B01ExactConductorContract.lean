import MCore.B01ConductorLevel

namespace MCore

/-- Semantic predicate supplied by a genuine Frey/local-conductor
formalization.  It is deliberately a parameter here: B01ConductorLevel alone
must not manufacture it. -/
abbrev B01ActualConductorLevel :=
  T59ResidualCandidate → Nat → Prop

/-- Exact cut between the certified structural conductor-level bookkeeping and
the still-open semantic statement that a level is the actual conductor level
of the concrete Frey object. -/
structure B01ExactConductorContract
    (ActualConductor : B01ActualConductorLevel)
    (d : T59ResidualCandidate) : Prop where
  level : Nat
  structural : B01ConductorLevel d level
  actual : ActualConductor d level

theorem b01_exact_conductor_contract_exposes_actual
    {ActualConductor : B01ActualConductorLevel}
    {d : T59ResidualCandidate}
    (C : B01ExactConductorContract ActualConductor d) :
    ∃ N : Nat, B01ConductorLevel d N ∧ ActualConductor d N :=
  ⟨C.level, C.structural, C.actual⟩

#print axioms MCore.b01_exact_conductor_contract_exposes_actual

end MCore
