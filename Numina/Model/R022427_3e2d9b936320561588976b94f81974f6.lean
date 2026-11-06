import Mathlib

theorem algebra_136720 (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A = !![3, -1, 3; 2, -1, 4; 1, 2, -3]) :
    A⁻¹ = !![1/2, -3/10, 1/10; -1, 6/5, 3/5; -1/2, 7/10, 1/10] := by
  rw [hA]
  simp [Matrix.inv, Matrix.det_fin_three, Matrix.mul_fin_three]
  all_goals
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num