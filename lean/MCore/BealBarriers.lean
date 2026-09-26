import MCore.BealViaABC

namespace MCore

/-!
BEAL ROUTE BARRIERS

These are provenance/coverage records, not proof terms for Beal.
-/

inductive BealBarrierStatus
  | scopeLimited
  | openMath
  | falsifiedFormulation
  deriving DecidableEq, Repr

structure BealBarrierRecord where
  id : String
  route : String
  source : String
  coverage : String
  limitation : String
  status : BealBarrierStatus

def darmonGranvilleBarrier : BealBarrierRecord :=
  { id := "D7-DARMON-GRANVILLE-1995"
    route := "generalized Fermat finiteness for fixed signature"
    source := "Darmon-Granville, Bull. LMS 27 (1995), 513-543"
    coverage := "fixed exponent signature in the hyperbolic regime"
    limitation := "does not itself provide a uniform effective Beal proof over all exponent triples"
    status := .scopeLimited }

def directFreyMixedExponentBarrier : BealBarrierRecord :=
  { id := "D7-FREY-MIXED-EXPONENT"
    route := "single direct Frey/level-lowering argument for arbitrary (x,y,z)"
    source := "repository B01/B02 frontier plus generalized-Fermat literature"
    coverage := "certified local/multiplicative-reduction prefix and selected signatures"
    limitation := "uniform conductor/level/newform elimination for arbitrary mixed exponents remains OPEN_MATH"
    status := .openMath }

def bealBarrierIndex : List BealBarrierRecord :=
  [darmonGranvilleBarrier, directFreyMixedExponentBarrier]

end MCore
