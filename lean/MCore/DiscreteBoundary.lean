import MCore.BealSpecification

namespace MCore

/-- The strict exponent hypothesis excludes the exponent boundary 0,1,2. -/
theorem exponent_three_le (d : BealData) : 3 ≤ d.x ∧ 3 ≤ d.y ∧ 3 ≤ d.z := by
  omega

/-- Positivity excludes zero bases. -/
theorem bases_ne_zero (d : BealData) : d.A ≠ 0 ∧ d.B ≠ 0 ∧ d.C ≠ 0 := by
  omega

/-- The admissible exponent region is discrete; exponent 2 is outside it. -/
theorem exponent_two_excluded (d : BealData) : d.x ≠ 2 ∧ d.y ≠ 2 ∧ d.z ≠ 2 := by
  omega

/-- Every represented candidate carries exactly the equation used by the conjecture. -/
theorem candidate_equation (d : BealData) : d.A ^ d.x + d.B ^ d.y = d.C ^ d.z :=
  d.equation

end MCore
