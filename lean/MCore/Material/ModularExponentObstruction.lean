import MCore.GCDLowerBoundProducer

namespace MCore

/-- If p divides all three exponents, it divides each exponent-weighted
valuation. This arithmetic fact alone does not establish level lowering. -/
theorem commonExponentPrime_dvd_weighted
    (p x y z va vb vc : Nat)
    (hx : p ∣ x) (hy : p ∣ y) (hz : p ∣ z) :
    p ∣ 2 * x * va ∧ p ∣ 2 * y * vb ∧ p ∣ 2 * z * vc := by
  constructor
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hx 2) va
  constructor
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hy 2) vb
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hz 2) vc

/-- A divisor of the product of the exponents need not divide every
exponent: p=5, (x,y,z)=(5,3,3). -/
theorem productExponentPrime_not_universal :
    ∃ p x y z : Nat,
      Nat.Prime p ∧ 2 < x ∧ 2 < y ∧ 2 < z ∧
      p ∣ x * y * z ∧ ¬ (p ∣ x ∧ p ∣ y ∧ p ∣ z) := by
  refine ⟨5, 5, 3, 3, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · decide
  · decide

end MCore
