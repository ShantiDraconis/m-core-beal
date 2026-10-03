import MCore.GCDLowerBoundProducer
import MCore.BealDirectProducer

namespace MCore

/-!
# Concrete Beal terminal law

This file identifies the exact certification and refutation predicates already
present in this repository. No new arithmetic hypothesis is introduced.
-/

/-- The concrete scalar defect on an admissible Beal datum. -/
def BealGCDDefect (d : BealData) : Nat :=
  Nat.gcd d.a (Nat.gcd d.b d.c) - 1

/-- Certification is exactly the existing Beal conjecture. -/
def BealTerminalCertifies : Prop :=
  BealConjecture

/-- Refutation is the existence of one admissible primitive solution. -/
def BealTerminalRefutes : Prop :=
  ∃ d : BealData, Nat.gcd d.a (Nat.gcd d.b d.c) ≤ 1

theorem beal_terminal_certifies_iff_gcdLowerBound :
    BealTerminalCertifies ↔ GCDLowerBoundProducer := by
  exact bealConjecture_iff_gcdLowerBoundProducer

theorem beal_terminal_refutes_iff_counterexample :
    BealTerminalRefutes ↔ ∃ d : BealData, BealCounterexample d := by
  constructor
  · rintro ⟨d, hg⟩
    refine ⟨d, ?_⟩
    intro hprime
    have hgt : 1 < Nat.gcd d.a (Nat.gcd d.b d.c) :=
      (commonPrime_iff_one_lt_nestedGCD d).mp hprime
    omega
  · rintro ⟨d, hcounter⟩
    refine ⟨d, ?_⟩
    by_contra hnot
    have hgt : 1 < Nat.gcd d.a (Nat.gcd d.b d.c) := by omega
    exact hcounter ((commonPrime_iff_one_lt_nestedGCD d).mpr hgt)

theorem not_beal_terminal_certifies_iff_refutes :
    ¬ BealTerminalCertifies ↔ BealTerminalRefutes := by
  classical
  constructor
  · intro h
    by_contra href
    have hg : GCDLowerBoundProducer := by
      intro d
      by_contra hle
      exact href ⟨d, by omega⟩
    exact h ((bealConjecture_iff_gcdLowerBoundProducer).2 hg)
  · rintro ⟨d, hg⟩ hcert
    have hgt : 1 < Nat.gcd d.a (Nat.gcd d.b d.c) :=
      (commonPrime_iff_one_lt_nestedGCD d).mp (hcert d)
    omega

theorem beal_terminal_cert_refute_disjoint :
    ¬ (BealTerminalCertifies ∧ BealTerminalRefutes) := by
  rintro ⟨hcert, href⟩
  exact (not_beal_terminal_certifies_iff_refutes.2 href) hcert

#print axioms MCore.beal_terminal_certifies_iff_gcdLowerBound
#print axioms MCore.beal_terminal_refutes_iff_counterexample
#print axioms MCore.not_beal_terminal_certifies_iff_refutes
#print axioms MCore.beal_terminal_cert_refute_disjoint

end MCore
