import MCore.T9

namespace MCore

/-- Core power-add identity, kept local so exponent normalization does not
    require an external algebra package. -/
theorem T10_pow_add (a m n : Nat) :
    a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, Nat.mul_assoc]

/-- Reassociate a power so a chosen divisor of the exponent becomes the
    outer exponent. -/
theorem T10_pow_mul_outer (a k r : Nat) :
    (a ^ k) ^ r = a ^ (k * r) := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [Nat.pow_succ, ih, Nat.mul_succ, T10_pow_add]

/-- A primitive Beal candidate in reduced exponent signature: every outer
    exponent is either 4 or a prime greater than 2. -/
structure T10ReducedPrimitiveSolution where
  a : Nat
  b : Nat
  c : Nat
  x : Nat
  y : Nat
  z : Nat
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  x_reduced : T7ReducedExponent x
  y_reduced : T7ReducedExponent y
  z_reduced : T7ReducedExponent z
  equation : a ^ x + b ^ y = c ^ z
  primitive : ¬ ∃ q : Nat, CommonDivisor q a b c

def T10ReducedScientificFrontier : Prop :=
  ¬ Nonempty T10ReducedPrimitiveSolution

/-- Every T6 primitive candidate can be normalized to a T10 candidate while
    preserving its equation and primitiveness. -/
theorem T10_reduce_primitive_solution
    (s : T6PrimitiveSolution) : T10ReducedPrimitiveSolution := by
  rcases T7_exponent_reduction s.x_gt_two with ⟨rx, kx, hx, hrx⟩
  rcases T7_exponent_reduction s.y_gt_two with ⟨ry, ky, hy, hry⟩
  rcases T7_exponent_reduction s.z_gt_two with ⟨rz, kz, hz, hrz⟩
  have hax : (s.a ^ kx) ^ rx = s.a ^ s.x := by
    calc
      (s.a ^ kx) ^ rx = s.a ^ (kx * rx) := T10_pow_mul_outer s.a kx rx
      _ = s.a ^ (rx * kx) := by rw [Nat.mul_comm kx rx]
      _ = s.a ^ s.x := (congrArg (fun n : Nat => s.a ^ n) hx).symm
  have hby : (s.b ^ ky) ^ ry = s.b ^ s.y := by
    calc
      (s.b ^ ky) ^ ry = s.b ^ (ky * ry) := T10_pow_mul_outer s.b ky ry
      _ = s.b ^ (ry * ky) := by rw [Nat.mul_comm ky ry]
      _ = s.b ^ s.y := (congrArg (fun n : Nat => s.b ^ n) hy).symm
  have hcz : (s.c ^ kz) ^ rz = s.c ^ s.z := by
    calc
      (s.c ^ kz) ^ rz = s.c ^ (kz * rz) := T10_pow_mul_outer s.c kz rz
      _ = s.c ^ (rz * kz) := by rw [Nat.mul_comm kz rz]
      _ = s.c ^ s.z := (congrArg (fun n : Nat => s.c ^ n) hz).symm
  refine
    { a := s.a ^ kx
      b := s.b ^ ky
      c := s.c ^ kz
      x := rx
      y := ry
      z := rz
      a_pos := Nat.pow_pos s.a_pos
      b_pos := Nat.pow_pos s.b_pos
      c_pos := Nat.pow_pos s.c_pos
      x_reduced := hrx
      y_reduced := hry
      z_reduced := hrz
      equation := ?_
      primitive := T9_powered_primitive_unconditional s.primitive }
  calc
    (s.a ^ kx) ^ rx + (s.b ^ ky) ^ ry
        = s.a ^ s.x + s.b ^ s.y := congrArg₂ (fun u v : Nat => u + v) hax hby
    _ = s.c ^ s.z := s.equation
    _ = (s.c ^ kz) ^ rz := hcz.symm

/-- A reduced candidate is already a T6 primitive candidate. -/
def T10_to_T6 (s : T10ReducedPrimitiveSolution) : T6PrimitiveSolution :=
  { a := s.a
    b := s.b
    c := s.c
    x := s.x
    y := s.y
    z := s.z
    a_pos := s.a_pos
    b_pos := s.b_pos
    c_pos := s.c_pos
    x_gt_two := s.x_reduced.1
    y_gt_two := s.y_reduced.1
    z_gt_two := s.z_reduced.1
    equation := s.equation
    primitive := s.primitive }

/-- T10 is an exact normalization, not a weakening: primitive candidates
    exist iff reduced-signature primitive candidates exist. -/
theorem T10_candidate_iff_reduced :
    Nonempty T6PrimitiveSolution ↔ Nonempty T10ReducedPrimitiveSolution := by
  constructor
  · rintro ⟨s⟩
    exact ⟨T10_reduce_primitive_solution s⟩
  · rintro ⟨s⟩
    exact ⟨T10_to_T6 s⟩

theorem T10_frontier_iff_reduced :
    T6ScientificFrontier ↔ T10ReducedScientificFrontier := by
  unfold T6ScientificFrontier T10ReducedScientificFrontier
  exact not_congr T10_candidate_iff_reduced

theorem T10_beal_iff_reduced_frontier :
    BealConjecture ↔ T10ReducedScientificFrontier :=
  T6_beal_iff_frontier.trans T10_frontier_iff_reduced

#print axioms MCore.T10_pow_add
#print axioms MCore.T10_pow_mul_outer
#print axioms MCore.T10_reduce_primitive_solution
#print axioms MCore.T10_candidate_iff_reduced
#print axioms MCore.T10_beal_iff_reduced_frontier

end MCore
