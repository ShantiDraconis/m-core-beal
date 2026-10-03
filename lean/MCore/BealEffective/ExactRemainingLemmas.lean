import MCore.BealEffectiveKernel

namespace MCore.BealEffective

/--
A reusable subcase eliminator: any proof that a Beal datum cannot have
`gcd3 = 1` immediately yields the strict terminal lower bound for that datum.
-/
theorem lowerBound_of_gcd3_ne_one
    (d : BealData)
    (hNe : gcd3 d ≠ 1) :
    1 < gcd3 d := by
  by_contra h
  exact hNe (gcd3_eq_one_of_not_lowerBound d h)

/--
Equivalent pointwise research target: it suffices to rule out `gcd3 = 1`
for every admissible Beal datum.
-/
theorem exactRemaining_of_no_gcd3_one
    (h : ∀ d : BealData, gcd3 d ≠ 1) :
    ExactRemainingObligation := by
  intro d
  exact lowerBound_of_gcd3_ne_one d (h d)

/--
Any certified class of data can be removed from the open residue by proving
that class incompatible with gcd3 = 1.
-/
structure GCDOneExcludedClass where
  contains : BealData → Prop
  exclude : ∀ d : BealData, contains d → gcd3 d ≠ 1

theorem lowerBound_on_excludedClass
    (C : GCDOneExcludedClass)
    {d : BealData}
    (hd : C.contains d) :
    1 < gcd3 d :=
  lowerBound_of_gcd3_ne_one d (C.exclude d hd)

#print axioms MCore.BealEffective.lowerBound_of_gcd3_ne_one
#print axioms MCore.BealEffective.exactRemaining_of_no_gcd3_one
#print axioms MCore.BealEffective.lowerBound_on_excludedClass

end MCore.BealEffective
