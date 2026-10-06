import MCore.OpenMath.BealQ10EndpointLattice

namespace MCore.OpenMath.BealQ10

inductive EndpointAtom where
  | open
  | closed
  deriving DecidableEq, Repr

abbrev EndpointWord := List EndpointAtom

def W_OPEN : EndpointWord := [.open]
def W_CLOSED : EndpointWord := [.closed]

def W_OPEN_CLOSED : EndpointWord := [.open, .closed]
def W_CLOSED_OPEN : EndpointWord := [.closed, .open]
def W_OPEN_OPEN : EndpointWord := [.open, .open]
def W_CLOSED_CLOSED : EndpointWord := [.closed, .closed]

def W_OPEN_OPEN_OPEN : EndpointWord := [.open, .open, .open]
def W_CLOSED_CLOSED_CLOSED : EndpointWord := [.closed, .closed, .closed]
def W_OPEN_OPEN_CLOSED : EndpointWord := [.open, .open, .closed]
def W_OPEN_CLOSED_OPEN : EndpointWord := [.open, .closed, .open]
def W_CLOSED_OPEN_OPEN : EndpointWord := [.closed, .open, .open]
def W_OPEN_CLOSED_CLOSED : EndpointWord := [.open, .closed, .closed]
def W_CLOSED_OPEN_CLOSED : EndpointWord := [.closed, .open, .closed]
def W_CLOSED_CLOSED_OPEN : EndpointWord := [.closed, .closed, .open]

def W_FULL : EndpointWord := [.open, .open, .closed, .closed]

theorem word_open : W_OPEN = [.open] := rfl
theorem word_closed : W_CLOSED = [.closed] := rfl

theorem word_open_closed : W_OPEN_CLOSED = [.open, .closed] := rfl
theorem word_closed_open : W_CLOSED_OPEN = [.closed, .open] := rfl
theorem word_open_open : W_OPEN_OPEN = [.open, .open] := rfl
theorem word_closed_closed : W_CLOSED_CLOSED = [.closed, .closed] := rfl

theorem word_open_open_open : W_OPEN_OPEN_OPEN = [.open, .open, .open] := rfl
theorem word_closed_closed_closed : W_CLOSED_CLOSED_CLOSED = [.closed, .closed, .closed] := rfl
theorem word_open_open_closed : W_OPEN_OPEN_CLOSED = [.open, .open, .closed] := rfl
theorem word_open_closed_open : W_OPEN_CLOSED_OPEN = [.open, .closed, .open] := rfl
theorem word_closed_open_open : W_CLOSED_OPEN_OPEN = [.closed, .open, .open] := rfl
theorem word_open_closed_closed : W_OPEN_CLOSED_CLOSED = [.open, .closed, .closed] := rfl
theorem word_closed_open_closed : W_CLOSED_OPEN_CLOSED = [.closed, .open, .closed] := rfl
theorem word_closed_closed_open : W_CLOSED_CLOSED_OPEN = [.closed, .closed, .open] := rfl

theorem word_full :
    W_FULL = [.open, .open, .closed, .closed] := rfl

def wordCollapse (w : EndpointWord) : CanonicalEndpointState :=
  let hasOpen := w.any (fun a => a == .open)
  let hasClosed := w.any (fun a => a == .closed)
  match hasOpen, hasClosed with
  | false, false => .empty
  | true, false => .openOnly
  | false, true => .closedOnly
  | true, true => .full

@[simp] theorem collapse_W_OPEN : wordCollapse W_OPEN = .openOnly := by rfl
@[simp] theorem collapse_W_CLOSED : wordCollapse W_CLOSED = .closedOnly := by rfl

@[simp] theorem collapse_W_OPEN_CLOSED : wordCollapse W_OPEN_CLOSED = .full := by rfl
@[simp] theorem collapse_W_CLOSED_OPEN : wordCollapse W_CLOSED_OPEN = .full := by rfl
@[simp] theorem collapse_W_OPEN_OPEN : wordCollapse W_OPEN_OPEN = .openOnly := by rfl
@[simp] theorem collapse_W_CLOSED_CLOSED : wordCollapse W_CLOSED_CLOSED = .closedOnly := by rfl

@[simp] theorem collapse_W_OPEN_OPEN_OPEN : wordCollapse W_OPEN_OPEN_OPEN = .openOnly := by rfl
@[simp] theorem collapse_W_CLOSED_CLOSED_CLOSED : wordCollapse W_CLOSED_CLOSED_CLOSED = .closedOnly := by rfl
@[simp] theorem collapse_W_OPEN_OPEN_CLOSED : wordCollapse W_OPEN_OPEN_CLOSED = .full := by rfl
@[simp] theorem collapse_W_OPEN_CLOSED_OPEN : wordCollapse W_OPEN_CLOSED_OPEN = .full := by rfl
@[simp] theorem collapse_W_CLOSED_OPEN_OPEN : wordCollapse W_CLOSED_OPEN_OPEN = .full := by rfl
@[simp] theorem collapse_W_OPEN_CLOSED_CLOSED : wordCollapse W_OPEN_CLOSED_CLOSED = .full := by rfl
@[simp] theorem collapse_W_CLOSED_OPEN_CLOSED : wordCollapse W_CLOSED_OPEN_CLOSED = .full := by rfl
@[simp] theorem collapse_W_CLOSED_CLOSED_OPEN : wordCollapse W_CLOSED_CLOSED_OPEN = .full := by rfl

@[simp] theorem collapse_W_FULL : wordCollapse W_FULL = .full := by rfl

theorem open_closed_order_distinct :
    W_OPEN_CLOSED ≠ W_CLOSED_OPEN := by decide

theorem triple_mixed_words_pairwise_examples :
    W_OPEN_OPEN_CLOSED ≠ W_OPEN_CLOSED_OPEN ∧
    W_OPEN_CLOSED_OPEN ≠ W_CLOSED_OPEN_OPEN ∧
    W_OPEN_CLOSED_CLOSED ≠ W_CLOSED_OPEN_CLOSED ∧
    W_CLOSED_OPEN_CLOSED ≠ W_CLOSED_CLOSED_OPEN := by
  decide

structure EndpointCube3Certificate : Prop where
  open_exists : W_OPEN = [.open]
  closed_exists : W_CLOSED = [.closed]
  oc_exists : W_OPEN_CLOSED = [.open, .closed]
  co_exists : W_CLOSED_OPEN = [.closed, .open]
  oo_exists : W_OPEN_OPEN = [.open, .open]
  cc_exists : W_CLOSED_CLOSED = [.closed, .closed]
  ooo_exists : W_OPEN_OPEN_OPEN = [.open, .open, .open]
  ccc_exists : W_CLOSED_CLOSED_CLOSED = [.closed, .closed, .closed]
  ooc_exists : W_OPEN_OPEN_CLOSED = [.open, .open, .closed]
  oco_exists : W_OPEN_CLOSED_OPEN = [.open, .closed, .open]
  coo_exists : W_CLOSED_OPEN_OPEN = [.closed, .open, .open]
  occ_exists : W_OPEN_CLOSED_CLOSED = [.open, .closed, .closed]
  coc_exists : W_CLOSED_OPEN_CLOSED = [.closed, .open, .closed]
  cco_exists : W_CLOSED_CLOSED_OPEN = [.closed, .closed, .open]
  full_exists : W_FULL = [.open, .open, .closed, .closed]
  full_collapses : wordCollapse W_FULL = .full
  full_material : FullMaterialState ↔ GlobalExternalCertificateState

theorem endpointCube3Certificate : EndpointCube3Certificate := by
  exact {
    open_exists := rfl
    closed_exists := rfl
    oc_exists := rfl
    co_exists := rfl
    oo_exists := rfl
    cc_exists := rfl
    ooo_exists := rfl
    ccc_exists := rfl
    ooc_exists := rfl
    oco_exists := rfl
    coo_exists := rfl
    occ_exists := rfl
    coc_exists := rfl
    cco_exists := rfl
    full_exists := rfl
    full_collapses := rfl
    full_material := Iff.rfl
  }

#print axioms MCore.OpenMath.BealQ10.endpointCube3Certificate
#print axioms MCore.OpenMath.BealQ10.open_closed_order_distinct
#print axioms MCore.OpenMath.BealQ10.triple_mixed_words_pairwise_examples

end MCore.OpenMath.BealQ10
