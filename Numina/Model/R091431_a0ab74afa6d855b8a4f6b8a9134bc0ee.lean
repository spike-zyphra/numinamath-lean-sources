import Mathlib

open Matrix Real

theorem calculus_16071 (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A = !![7/25, -24/25; -24/25, -7/25]) :
    ∃ v : Fin 2 → ℝ, v 0 > 0 ∧ v 1 = -3 * v 0 / 4 ∧
      A * !![v 0; v 1] = !![v 0; v 1] := by
  use λ i => match i with 
    | 0 => 4
    | 1 => -3
    | _ => 0
  constructor
  · norm_num -- Prove that the first component is positive (4 > 0).
  constructor
  · -- Verify that the second component equals -3/4 times the first component.
    norm_num
  · -- Show that when the matrix A is multiplied by the vector v, it equals v.
    rw [hA]
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul]
    all_goals norm_num