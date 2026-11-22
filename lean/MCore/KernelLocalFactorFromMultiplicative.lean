import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction

namespace MCore

open Polynomial

/--
Kernel-first local consequence of genuine multiplicative reduction.

This theorem does not assume a conductor exponent or a lowered level.
It only extracts the exact two possible local-polynomial shapes from the
Mathlib reduction predicate, so it can be used upstream of the conductor gate.
-/
theorem localPolynomial_eq_one_sub_or_add_X_of_multiplicative
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K)
    (hmult : (W.minimal R).HasMultiplicativeReduction R) :
    W.localPolynomial R = 1 - X ∨
      W.localPolynomial R = 1 + X := by
  classical
  let W' := W.minimal R
  have hnotgood : ¬ W'.HasGoodReduction R :=
    hmult.not_hasGoodReduction
  by_cases hsplit : W'.HasSplitMultiplicativeReduction R
  · left
    simp [WeierstrassCurve.localPolynomial, W', hnotgood, hsplit]
  · right
    simp [WeierstrassCurve.localPolynomial, W', hnotgood, hsplit, hmult]

/-- Multiplicative reduction forces the local polynomial to have degree one. -/
theorem localPolynomial_natDegree_eq_one_of_multiplicative
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K)
    (hmult : (W.minimal R).HasMultiplicativeReduction R) :
    (W.localPolynomial R).natDegree = 1 := by
  rcases localPolynomial_eq_one_sub_or_add_X_of_multiplicative R W hmult with h | h
  · rw [h]
    have hp : (1 - X : ℤ[X]) = -(X - C 1) := by
      ext n
      simp [sub_eq_add_neg]
    rw [hp, natDegree_neg, natDegree_X_sub_C]
  · rw [h]
    have hp : (1 + X : ℤ[X]) = X + C 1 := by
      simp [add_comm]
    rw [hp, natDegree_X_add_C]

#print axioms MCore.localPolynomial_eq_one_sub_or_add_X_of_multiplicative
#print axioms MCore.localPolynomial_natDegree_eq_one_of_multiplicative

end MCore
