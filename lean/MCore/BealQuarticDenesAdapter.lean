import MCore.BealQuarticGeneralizedFermatReduction

namespace MCore

/-- Positive primitive solution datum for Denes/Darmon-Merel equation. -/
structure PrimitiveDenesSolution (n : Nat) where
  X : Nat
  Y : Nat
  Z : Nat
  X_pos : 0 < X
  Y_pos : 0 < Y
  Z_pos : 0 < Z
  equation : X ^ n + Y ^ n = 2 * Z ^ n
  primitive : Nat.gcd X (Nat.gcd Y Z) = 1
  nontrivial : ¬ (X = Y ∧ Y = Z)

/--
The a-even x=z=4 residual branch produces a positive primitive nontrivial
Denes solution of exponent y.
-/
theorem T59_xz_four_a_even_to_primitive_denes
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (haEven : T12Even d.a) :
    Nonempty (PrimitiveDenesSolution d.y) := by
  rcases T59_xz_four_a_even_generalized_fermat d hx hz haEven with
    ⟨u,v,w,hsub,hadd,hquad,hden⟩
  rcases T59_xz_four_a_even_uv_coprime d hx hz haEven with
    ⟨u',v',hsub',hadd',huv⟩
  have huEq : u = u' := by
    have hyPos : 0 < d.y :=
      Nat.lt_trans (by decide : 0 < 2) d.y_reduced.1
    apply Nat.pow_left_injective hyPos
    rw [← hsub, ← hsub']
  have hvEq : v = v' := by
    have hyPos : 0 < d.y :=
      Nat.lt_trans (by decide : 0 < 2) d.y_reduced.1
    apply Nat.pow_left_injective hyPos
    rw [← hadd, ← hadd']
  subst u'
  subst v'
  let X := u ^ 2
  let Y := v ^ 2
  let Z := w
  have hXeq :
      X ^ d.y + Y ^ d.y = 2 * Z ^ d.y := by
    simpa [X,Y,Z,pow_mul,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hden
  have hsubPos : 0 < d.c - d.a := by
    have hac_lt : d.a < d.c := by
      have heq' : d.b ^ d.y + d.a ^ d.x = d.c ^ d.z := by
        simpa [Nat.add_comm] using d.equation
      exact T21_right_same_exponent_gap d.b_pos heq' (by simpa [hx,hz])
    exact Nat.zero_lt_sub_of_lt hac_lt
  have huPos : 0 < u := by
    rw [hsub] at hsubPos
    exact Nat.pos_of_pow_pos _ hsubPos
  have haddPos : 0 < d.c + d.a := Nat.add_pos_left d.c d.a_pos
  have hvPos : 0 < v := by
    rw [hadd] at haddPos
    exact Nat.pos_of_pow_pos _ haddPos
  have hwPos : 0 < w := by
    have hqPos : 0 < d.c ^ 2 + d.a ^ 2 := by
      exact Nat.add_pos_left _ (Nat.pow_pos d.c_pos)
    rw [hquad] at hqPos
    exact Nat.pos_of_pow_pos _ hqPos
  have hXYcop : Nat.Coprime X Y := by
    simpa [X,Y] using Nat.Coprime.pow 2 2 huv
  have hprimitive : Nat.gcd X (Nat.gcd Y Z) = 1 := by
    have hXYg : Nat.gcd X Y = 1 := hXYcop.gcd_eq_one
    have hdiv : Nat.gcd X (Nat.gcd Y Z) ∣ Nat.gcd X Y := by
      apply Nat.dvd_gcd
      · exact Nat.gcd_dvd_left _ _
      · exact Nat.dvd_trans (Nat.gcd_dvd_right X (Nat.gcd Y Z))
          (Nat.gcd_dvd_left Y Z)
    have hone : Nat.gcd X (Nat.gcd Y Z) ∣ 1 := by
      simpa [hXYg] using hdiv
    exact Nat.dvd_one.mp hone
  have hneqXY : X ≠ Y := by
    intro hXY
    have huvEq : u = v := by
      have : u ^ 2 = v ^ 2 := by simpa [X,Y] using hXY
      exact (Nat.pow_left_injective (by decide : 0 < (2:Nat))).mp this
    have hsumeq : d.c - d.a = d.c + d.a := by
      rw [hsub,hadd,huvEq]
    have ha0 : d.a = 0 := by omega
    exact (Nat.ne_of_gt d.a_pos) ha0
  exact ⟨{
    X := X
    Y := Y
    Z := Z
    X_pos := Nat.pow_pos huPos
    Y_pos := Nat.pow_pos hvPos
    Z_pos := hwPos
    equation := hXeq
    primitive := hprimitive
    nontrivial := by
      intro h
      exact hneqXY h.1
  }⟩

#print axioms MCore.T59_xz_four_a_even_to_primitive_denes

end MCore
