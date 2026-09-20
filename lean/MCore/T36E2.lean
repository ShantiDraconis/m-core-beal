import MCore.T36E1
import Mathlib.Tactic

namespace MCore

open WeierstrassCurve
open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum

/-- An integral Weierstrass model whose c4 is a unit in the DVR valuation is
    already minimal.  This is proved directly from Mathlib's definition of
    IsMinimal and the exact variable-change laws for c4 and Delta. -/
theorem T36E2_isMinimal_of_integral_c4_unit
    {R K : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K}
    (hInt : WeierstrassCurve.IsIntegral R W)
    (hc4 :
      (IsDiscreteValuationRing.maximalIdeal R).valuation K W.c₄ = 1) :
    WeierstrassCurve.IsMinimal R W := by
  letI : WeierstrassCurve.IsIntegral R W := hInt
  refine ⟨?_⟩
  refine ⟨by simp, ?_⟩
  intro C hC _
  letI : WeierstrassCurve.IsIntegral R (C • W) := hC
  simp only [one_smul]
  rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R (C • W)]
  rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R W]

  have hc4C_le :
      (IsDiscreteValuationRing.maximalIdeal R).valuation K (C • W).c₄ ≤ 1 := by
    rw [← WeierstrassCurve.integralModel_c₄_eq R (C • W)]
    exact
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one
        (IsDiscreteValuationRing.maximalIdeal R)
        (WeierstrassCurve.integralModel R (C • W)).c₄

  rw [WeierstrassCurve.variableChange_c₄] at hc4C_le
  simp only [map_mul, map_pow, hc4, mul_one] at hc4C_le

  have huInv_le :
      (IsDiscreteValuationRing.maximalIdeal R).valuation K
          ((C.u⁻¹ : K)) ≤ 1 := by
    exact (pow_le_one_iff (by decide : (4 : Nat) ≠ 0)).mp hc4C_le

  have huInv12_le :
      ((IsDiscreteValuationRing.maximalIdeal R).valuation K
          ((C.u⁻¹ : K))) ^ 12 ≤ 1 := by
    exact (pow_le_one_iff (by decide : (12 : Nat) ≠ 0)).mpr huInv_le

  rw [WeierstrassCurve.variableChange_Δ]
  simp only [map_mul, map_pow]
  simpa using
    (mul_le_mul_right'
      huInv12_le
      ((IsDiscreteValuationRing.maximalIdeal R).valuation K W.Δ))

/-- The Frey equation over the local ring Z_(p). -/
noncomputable def T36E2FreyCurveLocal
    (a b x y p : Nat) :
    WeierstrassCurve (T36CLocalRing p) :=
  (T36CFreyCurveZ a b x y).baseChange (T36CLocalRing p)

/-- The local Frey model base-changes to the exact fraction-field Frey model. -/
theorem T36E2_local_baseChange_eq_frac
    {a b x y p : Nat}
    [hP : (T36CPrimeIdeal p).IsPrime] :
    (T36E2FreyCurveLocal a b x y p).baseChange (FractionRing ℤ) =
      T36CFreyCurveFrac a b x y := by
  ext <;>
    simp [T36E2FreyCurveLocal, T36CFreyCurveFrac,
      IsScalarTower.algebraMap_apply ℤ (T36CLocalRing p) (FractionRing ℤ)]

/-- Therefore the exact Frey model used by E1 is integral over Z_(p). -/
theorem T36E2_freyFrac_isIntegral
    {a b x y p : Nat}
    [hP : (T36CPrimeIdeal p).IsPrime] :
    WeierstrassCurve.IsIntegral
      (T36CLocalRing p)
      (T36CFreyCurveFrac a b x y) := by
  refine ⟨?_⟩
  exact ⟨T36E2FreyCurveLocal a b x y p,
    (T36E2_local_baseChange_eq_frac (a := a) (b := b)
      (x := x) (y := y) (p := p)).symm⟩

/-- The T36 arithmetic package now forces minimality of the exact Frey model,
    once the local prime/DVR instances are installed. -/
theorem T36E2_package_minimal
    {a b c x y z p : Nat}
    (hPkg : T36OddLocalArithmeticPackage a b c x y z p)
    [hP : (T36CPrimeIdeal p).IsPrime]
    [hDVR : IsDiscreteValuationRing (T36CLocalRing p)] :
    WeierstrassCurve.IsMinimal
      (T36CLocalRing p)
      (T36CFreyCurveFrac a b x y) := by
  exact T36E2_isMinimal_of_integral_c4_unit
    (T36E2_freyFrac_isIntegral (a := a) (b := b)
      (x := x) (y := y) (p := p))
    (T36E1_package_c4_localDVR hPkg)

/-- With E1 valuations and E2 minimality, Mathlib's genuine
    HasMultiplicativeReduction class is constructible for the same Frey model. -/
theorem T36E2_package_multiplicative
    {a b c x y z p : Nat}
    (hPkg : T36OddLocalArithmeticPackage a b c x y z p)
    [hP : (T36CPrimeIdeal p).IsPrime]
    [hDVR : IsDiscreteValuationRing (T36CLocalRing p)] :
    (T36CFreyCurveFrac a b x y).HasMultiplicativeReduction
      (T36CLocalRing p) := by
  letI : WeierstrassCurve.IsMinimal
      (T36CLocalRing p)
      (T36CFreyCurveFrac a b x y) :=
    T36E2_package_minimal hPkg
  exact T36C_hasMultiplicativeReduction_of_local_data
    (T36E1_package_delta_localDVR hPkg)
    (T36E1_package_c4_localDVR hPkg)

/-- After E2, only the conductor exponent theorem remains in the odd-local
    semantic chain, provided this module compiles with zero sorryAx. -/
def T36E2ConductorExponentOneState : T36GapState :=
  .openBridge

#print axioms MCore.T36E2_isMinimal_of_integral_c4_unit
#print axioms MCore.T36E2_local_baseChange_eq_frac
#print axioms MCore.T36E2_freyFrac_isIntegral
#print axioms MCore.T36E2_package_minimal
#print axioms MCore.T36E2_package_multiplicative

end MCore
