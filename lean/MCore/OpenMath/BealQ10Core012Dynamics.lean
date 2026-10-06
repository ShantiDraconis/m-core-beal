import MCore.OpenMath.BealQ10TerminalCycle

namespace MCore.OpenMath.BealQ10

/-- Three-state structural code for the terminal search dynamics. -/
inductive CoreState where
  | left
  | core
  | right
  deriving DecidableEq, Repr

def CoreState.code : CoreState → Nat
  | .left => 0
  | .core => 1
  | .right => 2

/-- Reverse image exchanges the two boundary states and fixes the core. -/
def CoreState.reverse : CoreState → CoreState
  | .left => .right
  | .core => .core
  | .right => .left

/-- Tension collapses either boundary state into the core and leaves the core fixed. -/
def CoreState.tension : CoreState → CoreState
  | .left => .core
  | .core => .core
  | .right => .core

/-- Repulsion/reversal followed by tension still collapses to the core. -/
def CoreState.repulseThenTension (s : CoreState) : CoreState :=
  CoreState.tension (CoreState.reverse s)

/-- Torsion is modeled as reverse-tension-reverse; it also fixes the core image. -/
def CoreState.torsion (s : CoreState) : CoreState :=
  CoreState.reverse (CoreState.tension (CoreState.reverse s))

theorem reverse_involutive (s : CoreState) :
    CoreState.reverse (CoreState.reverse s) = s := by
  cases s <;> rfl

theorem tension_to_core (s : CoreState) :
    CoreState.tension s = .core := by
  cases s <;> rfl

theorem tension_idempotent (s : CoreState) :
    CoreState.tension (CoreState.tension s) = CoreState.tension s := by
  cases s <;> rfl

theorem reverse_core :
    CoreState.reverse .core = .core := by
  rfl

theorem repulsion_collapses (s : CoreState) :
    CoreState.repulseThenTension s = .core := by
  cases s <;> rfl

theorem torsion_collapses (s : CoreState) :
    CoreState.torsion s = .core := by
  cases s <;> rfl

/--
Both closed boundaries converge to the same fixed core, and repeating any of
the structural moves cannot create a fourth state or a new mathematical
parameter.
-/
structure Core012Certificate : Prop where
  left_code : CoreState.left.code = 0
  core_code : CoreState.core.code = 1
  right_code : CoreState.right.code = 2
  reverse_inv : ∀ s, CoreState.reverse (CoreState.reverse s) = s
  tension_fix : ∀ s, CoreState.tension s = .core
  tension_idem : ∀ s, CoreState.tension (CoreState.tension s) = CoreState.tension s
  repulsion_fix : ∀ s, CoreState.repulseThenTension s = .core
  torsion_fix : ∀ s, CoreState.torsion s = .core

theorem core012Certificate : Core012Certificate := by
  exact {
    left_code := rfl
    core_code := rfl
    right_code := rfl
    reverse_inv := reverse_involutive
    tension_fix := tension_to_core
    tension_idem := tension_idempotent
    repulsion_fix := repulsion_collapses
    torsion_fix := torsion_collapses
  }

#print axioms MCore.OpenMath.BealQ10.core012Certificate

end MCore.OpenMath.BealQ10
