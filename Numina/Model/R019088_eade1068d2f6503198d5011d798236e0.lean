import Mathlib

theorem algebra_154028 (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A = !![2, -1; 4, 3]) :
    A⁻¹ = !![3 / 10, 1 / 10; -2 / 5, 1 / 5] := by 
  rw [hA]
  ext i j 
  fin_cases i <;> fin_cases j <;> simp [Matrix.inv, Matrix.det_fin_two] 
  <;> norm_num