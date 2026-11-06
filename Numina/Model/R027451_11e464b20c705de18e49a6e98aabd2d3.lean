import Mathlib

open Matrix

theorem calculus_17485 {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A = !![0, 1; 3, 0]) :
    ∃ v : ℝ × ℝ, (A ^ 8 + A ^ 6 + A ^ 4 + A ^ 2 + 1) * !![v.1; v.2] = !![0; 11] ↔
    v = (0, 1 / 11) := by
  use (0, 1 / 11)
  rw [hA]
  simp [pow_succ, Matrix.mul_apply, Matrix.of_apply, Matrix.one_fin_two]
  all_goals norm_num [Fin.sum_univ_succ, Fin.sum_univ_zero]
  <;> linarith