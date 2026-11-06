import Mathlib

theorem algebra_13288 (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A = !![1, 2, 3; 4, 7, 10; 7, 10, 13]) :
    A.det = 0 := by
  rw [hA]
  simp [Matrix.det_fin_three, Matrix.det_fin_two]
  all_goals
    norm_num