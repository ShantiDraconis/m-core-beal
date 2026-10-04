import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

/-- Raw Frey discriminant kernel for Y^2 = X(X-a^x)(X+b^y). -/
def XYFreyDiscriminantKernel
    (a b x y : Nat) : Nat :=
  16 * (a ^ x) ^ 2 * (b ^ y) ^ 2 * (a ^ x + b ^ y) ^ 2

/-- Beal-normal form of the same raw discriminant. -/
def XYFreyDiscriminantBeal
    (a b c x y z : Nat) : Nat :=
  16 * (a ^ x) ^ 2 * (b ^ y) ^ 2 * (c ^ z) ^ 2

theorem xy_frey_discriminant_rewrite
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z) :
    XYFreyDiscriminantKernel a b x y =
      XYFreyDiscriminantBeal a b c x y z := by
  unfold XYFreyDiscriminantKernel XYFreyDiscriminantBeal
  rw [heq]

private def xyFreyData (r : ReducedPrimitiveCandidate) : BealData where
  a := r.a
  b := r.b
  c := r.c
  x := r.x
  y := r.y
  z := r.z
  a_pos := r.a_pos
  b_pos := r.b_pos
  c_pos := r.c_pos
  x_gt_two := r.x_reduced.1
  y_gt_two := r.y_reduced.1
  z_gt_two := r.z_reduced.1
  equation := r.equation

private theorem xyFreyPairwise
    (r : ReducedPrimitiveCandidate) :
    PairwisePrimitive r.a r.b r.c := by
  constructor
  · intro h
    exact r.no_common (ab_pair_forces_common (xyFreyData r) h)
  · constructor
    · intro h
      exact r.no_common (ac_pair_forces_common (xyFreyData r) h)
    · intro h
      exact r.no_common (bc_pair_forces_common (xyFreyData r) h)

private theorem xyFreyExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c :=
  exactlyOneEven_of_pairwise (xyFreyData r) (xyFreyPairwise r)

private theorem xyFrey_gcd_ab
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.a r.b = 1 := by
  by_contra hne
  have hpos : 0 < Nat.gcd r.a r.b :=
    Nat.gcd_pos_of_pos_left r.b r.a_pos
  have hgt : 1 < Nat.gcd r.a r.b := by omega
  exact (xyFreyPairwise r).1
    ⟨Nat.gcd r.a r.b, hgt,
      Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩

private theorem xyFrey_gcd_ac
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.a r.c = 1 := by
  by_contra hne
  have hpos : 0 < Nat.gcd r.a r.c :=
    Nat.gcd_pos_of_pos_left r.c r.a_pos
  have hgt : 1 < Nat.gcd r.a r.c := by omega
  exact (xyFreyPairwise r).2.1
    ⟨Nat.gcd r.a r.c, hgt,
      Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩

private theorem xyFrey_gcd_bc
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.b r.c = 1 := by
  by_contra hne
  have hpos : 0 < Nat.gcd r.b r.c :=
    Nat.gcd_pos_of_pos_left r.c r.b_pos
  have hgt : 1 < Nat.gcd r.b r.c := by omega
  exact (xyFreyPairwise r).2.2
    ⟨Nat.gcd r.b r.c, hgt,
      Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩

/--
Exact arithmetic packet supplied to the modular/Frey route for orbit A.
No conductor, modularity, irreducibility, or level-lowering conclusion is
stored here.
-/
structure XYFourPrimeFreyArithmeticPacket
    (r : ReducedPrimitiveCandidate) : Prop where
  hx : r.x = 4
  hy : r.y = 4
  hzPrime : OddPrimeExponent r.z
  equation : r.a ^ 4 + r.b ^ 4 = r.c ^ r.z
  pairwise :
    Nat.gcd r.a r.b = 1 ∧
    Nat.gcd r.a r.c = 1 ∧
    Nat.gcd r.b r.c = 1
  exactlyOneEven : ExactlyOneEven r.a r.b r.c
  rhsNotEven : ¬ Even r.c
  discriminant :
    XYFreyDiscriminantKernel r.a r.b r.x r.y =
      XYFreyDiscriminantBeal r.a r.b r.c r.x r.y r.z

private theorem xyFrey_even_pow8
    {n e : Nat}
    (hn : Even n)
    (he : 2 < e) :
    n ^ e % 8 = 0 := by
  rcases hn with ⟨k, hk⟩
  obtain ⟨m, hm⟩ : ∃ m : Nat, e = m + 3 := by
    refine ⟨e - 3, ?_⟩
    omega
  rw [hk, hm]
  simp [Nat.pow_add, Nat.mul_pow, Nat.mul_mod,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem xyFrey_pow_mod_congr
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

private theorem xyFrey_odd_fourth8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  have hres :
      n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have hpar : (n % 8) % 2 = 1 :=
      (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
    have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
    omega
  rcases hres with h | h | h | h
  all_goals
    have hc : n ^ 4 % 8 = (n % 8) ^ 4 % 8 := by
      apply xyFrey_pow_mod_congr
      simp
    rw [hc, h]

private theorem xyFrey_notEven_mod2_one
    (n : Nat) :
    (¬ Even n) ↔ n % 2 = 1 := by
  unfold Even
  constructor
  · intro h
    have hpos : 0 < n % 2 := Nat.emod_pos_of_not_dvd h
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  · intro hm hd
    have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega

private theorem xyFrey_rhs_not_even
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    ¬ Even r.c := by
  intro hc
  have hE := xyFreyExactlyOneEven r
  have haOdd : r.a % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact (xyFrey_notEven_mod2_one r.a).mp hB.1
    · exact (xyFrey_notEven_mod2_one r.a).mp hC.1
  have hbOdd : r.b % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact (xyFrey_notEven_mod2_one r.b).mp hA.2.1
    · exact False.elim (hB.2.2 hc)
    · exact (xyFrey_notEven_mod2_one r.b).mp hC.2.1
  have hA8 : r.a ^ 4 % 8 = 1 := xyFrey_odd_fourth8 haOdd
  have hB8 : r.b ^ 4 % 8 = 1 := xyFrey_odd_fourth8 hbOdd
  have hC8 : r.c ^ r.z % 8 = 0 :=
    xyFrey_even_pow8 hc r.z_reduced.1
  have hmod := congrArg (fun n : Nat => n % 8) r.equation
  have hbad : (1 + 1) % 8 = 0 := by
    simpa [hx, hy, Nat.add_mod, hA8, hB8, hC8] using hmod
  simp at hbad

def xyFourPrimeFreyArithmeticPacket
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4)
    (hzPrime : OddPrimeExponent r.z) :
    XYFourPrimeFreyArithmeticPacket r where
  hx := hx
  hy := hy
  hzPrime := hzPrime
  equation := by simpa [hx, hy] using r.equation
  pairwise := ⟨xyFrey_gcd_ab r, xyFrey_gcd_ac r, xyFrey_gcd_bc r⟩
  exactlyOneEven := xyFreyExactlyOneEven r
  rhsNotEven := xyFrey_rhs_not_even r hx hy
  discriminant := xy_frey_discriminant_rewrite r.equation

#print axioms MCore.BealEffective.OpenMath.xy_frey_discriminant_rewrite
#print axioms MCore.BealEffective.OpenMath.xyFourPrimeFreyArithmeticPacket

end OpenMath
end BealEffective
end MCore
