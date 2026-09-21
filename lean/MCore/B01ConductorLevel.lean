import MCore.T59
import Mathlib

namespace MCore

/-!
B01 conductor-level interface.

This is the project-local, mixed-exponent analogue of the structural
"conductor level" bookkeeping used by level-lowering arguments.  It does not
assert modularity, irreducibility, unramifiedness, or that such a level has
already been constructed.
-/

structure B01ConductorLevel (d : T59ResidualCandidate) (N : Nat) : Prop where
  pos : 0 < N
  squarefree : Squarefree N
  support :
    ∀ q : Nat, q.Prime → q ∣ N → q ∣ d.a * d.b * d.c

namespace B01ConductorLevel

variable {d : T59ResidualCandidate} {N M q : Nat}

theorem of_dvd
    (hN : B01ConductorLevel d N)
    (hMN : M ∣ N)
    (hM : 0 < M) :
    B01ConductorLevel d M := by
  refine ⟨hM, hN.squarefree.squarefree_of_dvd hMN, ?_⟩
  intro p hp hpM
  exact hN.support p hp (hpM.trans hMN)

theorem prime_support
    (hN : B01ConductorLevel d N)
    (hq : q.Prime)
    (hqN : q ∣ N) :
    q ∣ d.a * d.b * d.c :=
  hN.support q hq hqN

theorem prime_square_not_dvd
    (hN : B01ConductorLevel d N)
    (hq : q.Prime) :
    ¬ q ^ 2 ∣ N := by
  exact Nat.squarefree_iff_prime_squarefree.mp hN.squarefree q hq

theorem two_square_not_dvd
    (hN : B01ConductorLevel d N) :
    ¬ 4 ∣ N := by
  have h4 : (4 : Nat) = 2 ^ 2 := by norm_num
  rw [h4]
  exact hN.prime_square_not_dvd Nat.prime_two

theorem remove_prime_preserves
    (hN : B01ConductorLevel d N)
    (hq : q.Prime)
    (hqN : q ∣ N) :
    B01ConductorLevel d (N / q) := by
  have hqpos : 0 < q := hq.pos
  have hNpos : 0 < N := hN.pos
  have hdivpos : 0 < N / q := Nat.div_pos hqN hqpos
  apply hN.of_dvd (Nat.div_dvd_of_dvd hqN) hdivpos

#print axioms MCore.B01ConductorLevel.of_dvd
#print axioms MCore.B01ConductorLevel.prime_support
#print axioms MCore.B01ConductorLevel.prime_square_not_dvd
#print axioms MCore.B01ConductorLevel.two_square_not_dvd
#print axioms MCore.B01ConductorLevel.remove_prime_preserves

end B01ConductorLevel
end MCore
