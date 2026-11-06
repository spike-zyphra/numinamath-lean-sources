import Mathlib

open Matrix

theorem calculus_12012 {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A = !![9, 18; -6, -12]) :
    A⁻¹ = 0 := by 
  rw [hA]
  have h1 : Matrix.det ((!![9, 18; -6, -12] : Matrix (Fin 2) (Fin 2) ℝ)) = 0 := by 
    simp [Matrix.det_fin_two]
    all_goals norm_num
  -- Now with determinant zero, we need to show the inverse is zero matrix
  have h2 : ((!![9, 18; -6, -12] : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ = 0 := by
    rw [Matrix.inv]
    simp only [h1, div_zero, zero_mul]
    ext i j 
    fin_cases i <;> fin_cases j <;> aesop
  simpa using h2