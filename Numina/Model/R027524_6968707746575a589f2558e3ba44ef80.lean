import Mathlib

theorem calculus_22317 {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A⁻¹ = !![2, 1; 0, -3]) (hB : B⁻¹ = !![0, 5; -1, 1]) :
    (A * B)⁻¹ = !![0, -15; -2, -4] := by 
  have h1 : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by 
    simp [Matrix.mul_inv_rev]
  rw [h1, hA, hB]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    <;> norm_num