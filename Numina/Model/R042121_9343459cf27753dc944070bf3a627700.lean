import Mathlib

open Matrix Real

theorem algebra_154011 (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A = !![3, 1, 2; -1, 2, 5; 0, -4, 2]) :
    A.det = 82 := by
  rw [hA]
  simp [Matrix.det_fin_three, Fin.sum_univ_three, mul_add, add_mul]
  all_goals norm_num