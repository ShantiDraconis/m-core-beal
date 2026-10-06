import MCore.OpenMath.BealQ10DualEndpointState

namespace MCore.OpenMath.BealQ10

/-- Free multiplicity model before idempotent collapse. -/
structure EndpointMultiset where
  openCount : Nat
  closedCount : Nat
  deriving DecidableEq, Repr

def EndpointMultiset.add
    (a b : EndpointMultiset) : EndpointMultiset :=
  ⟨a.openCount + b.openCount, a.closedCount + b.closedCount⟩

def OPEN1 : EndpointMultiset := ⟨1, 0⟩
def CLOSED1 : EndpointMultiset := ⟨0, 1⟩

@[simp] theorem open_add_open :
    EndpointMultiset.add OPEN1 OPEN1 = ⟨2, 0⟩ := by
  rfl

@[simp] theorem closed_add_closed :
    EndpointMultiset.add CLOSED1 CLOSED1 = ⟨0, 2⟩ := by
  rfl

@[simp] theorem open_add_closed :
    EndpointMultiset.add OPEN1 CLOSED1 = ⟨1, 1⟩ := by
  rfl

/-- Idempotent quotient: only presence/absence of each endpoint matters. -/
inductive CanonicalEndpointState where
  | empty
  | openOnly
  | closedOnly
  | full
  deriving DecidableEq, Repr

def EndpointMultiset.collapse
    (s : EndpointMultiset) : CanonicalEndpointState :=
  match s.openCount = 0, s.closedCount = 0 with
  | true, true => .empty
  | false, true => .openOnly
  | true, false => .closedOnly
  | false, false => .full

theorem collapse_zero_zero :
    EndpointMultiset.collapse ⟨0, 0⟩ = .empty := by
  rfl

theorem collapse_open :
    EndpointMultiset.collapse ⟨1, 0⟩ = .openOnly := by
  rfl

theorem collapse_closed :
    EndpointMultiset.collapse ⟨0, 1⟩ = .closedOnly := by
  rfl

theorem collapse_full :
    EndpointMultiset.collapse ⟨1, 1⟩ = .full := by
  rfl

/-- Idempotence at the quotient level. -/
def canonJoin :
    CanonicalEndpointState → CanonicalEndpointState → CanonicalEndpointState
  | .empty, x => x
  | x, .empty => x
  | .openOnly, .openOnly => .openOnly
  | .closedOnly, .closedOnly => .closedOnly
  | .openOnly, .closedOnly => .full
  | .closedOnly, .openOnly => .full
  | .full, _ => .full
  | _, .full => .full

theorem canonJoin_open_idempotent :
    canonJoin .openOnly .openOnly = .openOnly := by
  rfl

theorem canonJoin_closed_idempotent :
    canonJoin .closedOnly .closedOnly = .closedOnly := by
  rfl

theorem canonJoin_open_closed_full :
    canonJoin .openOnly .closedOnly = .full := by
  rfl

theorem canonJoin_full_absorbing_left
    (x : CanonicalEndpointState) :
    canonJoin .full x = .full := by
  cases x <;> rfl

theorem canonJoin_full_absorbing_right
    (x : CanonicalEndpointState) :
    canonJoin x .full = .full := by
  cases x <;> rfl

/--
Material interpretation of the maximal state: FULL contains both endpoint
positions simultaneously, i.e. exactly an RPA DualEndpointState.
-/
def FullMaterialState : Prop := DualEndpointState

abbrev MathState : Prop := FullMaterialState
abbrev FinalRootState : Prop := FullMaterialState
abbrev GlobalExternalCertificateState : Prop := FullMaterialState

theorem full_iff_math :
    FullMaterialState ↔ MathState := Iff.rfl

theorem math_iff_finalRoot :
    MathState ↔ FinalRootState := Iff.rfl

theorem finalRoot_iff_globalExternal :
    FinalRootState ↔ GlobalExternalCertificateState := Iff.rfl

theorem fullMaterial_iff_endpoint :
    Nonempty FullMaterialState ↔ Nonempty Endpoint :=
  dualEndpointState_iff_endpoint

structure EndpointLatticeCertificate : Prop where
  openIdem : canonJoin .openOnly .openOnly = .openOnly
  closedIdem : canonJoin .closedOnly .closedOnly = .closedOnly
  mixedFull : canonJoin .openOnly .closedOnly = .full
  fullLeft : ∀ x, canonJoin .full x = .full
  fullRight : ∀ x, canonJoin x .full = .full
  fullMath : FullMaterialState ↔ MathState
  mathFinal : MathState ↔ FinalRootState
  finalGlobal : FinalRootState ↔ GlobalExternalCertificateState

theorem endpointLatticeCertificate :
    EndpointLatticeCertificate := by
  exact {
    openIdem := canonJoin_open_idempotent
    closedIdem := canonJoin_closed_idempotent
    mixedFull := canonJoin_open_closed_full
    fullLeft := canonJoin_full_absorbing_left
    fullRight := canonJoin_full_absorbing_right
    fullMath := full_iff_math
    mathFinal := math_iff_finalRoot
    finalGlobal := finalRoot_iff_globalExternal
  }

#print axioms MCore.OpenMath.BealQ10.endpointLatticeCertificate
#print axioms MCore.OpenMath.BealQ10.fullMaterial_iff_endpoint

end MCore.OpenMath.BealQ10
