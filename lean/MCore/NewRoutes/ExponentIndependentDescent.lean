namespace MCore.NewRoutes
structure ExponentIndependentDescent where
  Counterexample : Type
  measure : Counterexample → Nat
  transform : Counterexample → Counterexample
  strictDecrease : ∀ s, measure (transform s) < measure s
def MaterialTarget (R : ExponentIndependentDescent) : Prop :=
  ∀ s : R.Counterexample, False
end MCore.NewRoutes
