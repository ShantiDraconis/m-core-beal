import MCore.BealEffective.ReducedFamilies
import open_math.Beal_Reduced_ParityPressure

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem notEven_iff_modTwo_eq_one (n : Nat) :
    (¬ Even n) ↔ n % 2 = 1 := by
  unfold Even
  constructor
  · intro h
    have hpos : 0 < n % 2 := Nat.emod_pos_of_not_dvd h
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  · intro hmod hdvd
    have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega

/-- Odd fourth powers are 1 modulo 16. -/
theorem reduced_odd_fourth_mod_sixteen
    {n : Nat}
    (hodd : n % 2 = 1) :
    n ^ 4 % 16 = 1 := by
  have hpar : (n % 16) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 16)).trans hodd
  have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
  interval_cases h : n % 16 <;>
    simp [Nat.pow_mod, h] at hpar ⊢

/-- Even fourth powers are 0 modulo 16. -/
theorem reduced_even_fourth_mod_sixteen
    {n : Nat}
    (heven : Even n) :
    n ^ 4 % 16 = 0 := by
  unfold Even at heven
  rcases heven with ⟨k, rfl⟩
  simp [pow_succ, Nat.mul_mod]

/--
In the (4,4,p) orientation x=y=4, the right-hand base cannot be even.
This is purely elementary: exactly-one-even plus mod 16.
-/
theorem allFourLeft_no_rhs_even
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    ¬ Even r.c := by
  intro hc
  rcases reduced_exactlyOneEven r with hA | hB | hC
  · exact hA.2.2 hc
  · exact hB.2.2 hc
  ·
    have haOdd : r.a % 2 = 1 :=
      (notEven_iff_modTwo_eq_one r.a).mp hC.1
    have hbOdd : r.b % 2 = 1 :=
      (notEven_iff_modTwo_eq_one r.b).mp hC.2.1
    have hA16 : r.a ^ 4 % 16 = 1 :=
      reduced_odd_fourth_mod_sixteen haOdd
    have hB16 : r.b ^ 4 % 16 = 1 :=
      reduced_odd_fourth_mod_sixteen hbOdd
    have hC16 : r.c ^ r.z % 16 = 0 := by
      rcases hc with ⟨k, hk⟩
      subst r.c
      have hzPos : 0 < r.z := Nat.lt_trans (by decide : 0 < 2) r.z_reduced.1
      rcases r.z with _ | z
      · omega
      · simp [Nat.pow_succ, Nat.mul_mod]
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    simp [hx, hy, Nat.add_mod, hA16, hB16, hC16] at hmod

/--
The (4,4,p) orientation forces c^p = 1 mod 16.
This is the first material local invariant of the seven-family min-cut.
-/
theorem twoFour_xy_rhs_pow_mod_sixteen
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    r.c ^ r.z % 16 = 1 := by
  have hcOdd : ¬ Even r.c := allFourLeft_no_rhs_even r hx hy
  rcases reduced_exactlyOneEven r with hA | hB | hC
  ·
    have hbOdd : r.b % 2 = 1 :=
      (notEven_iff_modTwo_eq_one r.b).mp hA.2.1
    have hA16 : r.a ^ 4 % 16 = 0 :=
      reduced_even_fourth_mod_sixteen hA.1
    have hB16 : r.b ^ 4 % 16 = 1 :=
      reduced_odd_fourth_mod_sixteen hbOdd
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
  ·
    have haOdd : r.a % 2 = 1 :=
      (notEven_iff_modTwo_eq_one r.a).mp hB.1
    have hA16 : r.a ^ 4 % 16 = 1 :=
      reduced_odd_fourth_mod_sixteen haOdd
    have hB16 : r.b ^ 4 % 16 = 0 :=
      reduced_even_fourth_mod_sixteen hB.2.1
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
  · exact False.elim (hcOdd hC.2.2)

#print axioms MCore.BealEffective.OpenMath.reduced_odd_fourth_mod_sixteen
#print axioms MCore.BealEffective.OpenMath.reduced_even_fourth_mod_sixteen
#print axioms MCore.BealEffective.OpenMath.allFourLeft_no_rhs_even
#print axioms MCore.BealEffective.OpenMath.twoFour_xy_rhs_pow_mod_sixteen

end OpenMath
end BealEffective
end MCore
