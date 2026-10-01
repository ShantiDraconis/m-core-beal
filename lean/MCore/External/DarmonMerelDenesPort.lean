import MCore.BealQuarticDenesAdapter

namespace MCore

/--
Exact formal port specification for the classical Darmon--Merel theorem on
primitive nontrivial solutions of X^n + Y^n = 2 Z^n.

This structure is NOT inhabited here.  It is the precise external theorem
interface to be supplied by an independent formalization/import.
-/
structure DarmonMerelDenesTheorem : Prop where
  no_nontrivial_primitive :
    ∀ n : Nat,
      3 ≤ n →
      ¬ Nonempty (PrimitiveDenesSolution n)

/--
Once the published Darmon--Merel theorem is formally imported, the a-even
x=z=4 residual branch is eliminated with no Beal hypothesis.
-/
theorem T59_xz_four_a_even_eliminated_of_darmon_merel
    (DM : DarmonMerelDenesTheorem)
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    False := by
  have hy3 : 3 ≤ d.y := by
    omega
  exact (DM.no_nontrivial_primitive d.y hy3)
    (T59_xz_four_a_even_to_primitive_denes d hx hz haEven)

/--
Local producer for eliminating this exact orientation.
-/
structure XZFourAEvenEliminationProducer : Prop where
  eliminate :
    ∀ d : T59ResidualCandidate,
      d.x = 4 →
      d.z = 4 →
      T12Even d.a →
      False

def xzFourAEvenElimination_of_darmon_merel
    (DM : DarmonMerelDenesTheorem) :
    XZFourAEvenEliminationProducer where
  eliminate := fun d hx hz ha =>
    T59_xz_four_a_even_eliminated_of_darmon_merel DM d hx hz ha

#print axioms MCore.T59_xz_four_a_even_eliminated_of_darmon_merel
#print axioms MCore.xzFourAEvenElimination_of_darmon_merel

end MCore
