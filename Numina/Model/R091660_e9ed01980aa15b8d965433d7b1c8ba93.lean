import Mathlib

open Matrix

theorem calculus_23151 {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A = !![2, 7; 13, -2]) :
    ((A⁻¹)⁻¹ = A) := by
  rw [hA]
  simp [inv, Matrix.inv, Matrix.det, Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul]
  all_goals norm_num [Matrix.inv, Matrix.det, Matrix.mul_apply]
  <;> ring_nf <;> norm_num