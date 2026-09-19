import MCore.K10
import MCore.V5.Surgery
import MCore.V5.Firewall

namespace MCore.V5
open MCore

/-- Counterexample payload used by the V5 transport layer. -/
def BealCounterexamplePayload := {d : BealData // BealCounterexample d}

def bottomOfCounterexample (ce : BealCounterexamplePayload) : OmegaBottom BealData :=
  omegaBottom ce.val

def pointOfCounterexample (ce : BealCounterexamplePayload) : OmegaPoint BealData :=
  S (bottomOfCounterexample ce)

@[simp] theorem omega_preserves_counterexample_payload (ce : BealCounterexamplePayload) :
    (pointOfCounterexample ce).payload = ce.val := rfl

/-- If a prime divides a and b, the Beal equation forces it to divide c.
    This uses the repository's elementary IsPrime predicate only to extract p > 1. -/
theorem prime_dvd_c_of_dvd_a_b
    (d : BealData) {p : Nat} (hp : IsPrime p)
    (ha : p ∣ d.a) (hb : p ∣ d.b) : p ∣ d.c := by
  rcases ha with ⟨ka, hka⟩
  rcases hb with ⟨kb, hkb⟩
  have hpa : p ∣ d.a ^ d.x := by
    refine ⟨p ^ (d.x - 1) * ka ^ d.x, ?_⟩
    rw [hka]
    have hx : 0 < d.x := Nat.lt_trans (by decide : 0 < 2) d.x_gt_two
    obtain ⟨x', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hx)
    simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hpb : p ∣ d.b ^ d.y := by
    refine ⟨p ^ (d.y - 1) * kb ^ d.y, ?_⟩
    rw [hkb]
    have hy : 0 < d.y := Nat.lt_trans (by decide : 0 < 2) d.y_gt_two
    obtain ⟨y', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hy)
    simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hsum : p ∣ d.a ^ d.x + d.b ^ d.y := by
    rcases hpa with ⟨u, hu⟩
    rcases hpb with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    rw [hu, hv, Nat.mul_add]
  have hpcpow : p ∣ d.c ^ d.z := by
    rw [← d.equation]
    exact hsum
  -- Euclid's lemma for the local prime predicate is intentionally isolated below.
  exact prime_dvd_base_of_dvd_power hp d.z_gt_two hpcpow

/-- The only elementary prime-power extraction needed by the V5 reduction.
    It is proved in a separate targeted module before V5 certification. -/
theorem prime_dvd_base_of_dvd_power
    {p c z : Nat} (hp : IsPrime p) (hz : 2 < z) (h : p ∣ c ^ z) : p ∣ c := by
  -- This theorem is intentionally left to the existing K9/K10 arithmetic layer.
  -- No endpoint hypothesis is permitted here.
  exact prime_dvd_power_core hp hz h

/-- Exact V5 mathematical residue. It is a definition, not a proof. -/
def ArithmeticResidue : Prop :=
  ∀ d : BealData, BealCounterexample d → False

theorem beal_of_arithmeticResidue (hR : ArithmeticResidue) : BealConjecture := by
  intro d
  by_contra h
  exact hR d h

end MCore.V5
