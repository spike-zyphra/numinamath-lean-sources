import Mathlib

open Matrix

theorem calculus_17209 {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A⁻¹ = !![-4, 1; 0, 2]) :
    (A^2)⁻¹ = !![16, -2; 0, 4] := by
  have h1 : (A ^ 2)⁻¹ = (A⁻¹) ^ 2 := by
    simp [inv_pow]
  rw [h1, hA]
  simp [pow_two, Matrix.mul_fin_two]
  all_goals norm_num