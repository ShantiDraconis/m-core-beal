import MCore.Research.Beal.TernaryDefect

namespace MCore.Research.Beal

theorem counterprobe_one_two : ternaryD 1 2 = 3 := by native_decide
theorem counterprobe_one_three : ternaryD 1 3 = 7 := by native_decide

/-- Audit marker: positivity / Eisenstein support of D alone is not a contradiction. -/
def ternaryEisensteinRouteFrozen : Bool := true

end MCore.Research.Beal
