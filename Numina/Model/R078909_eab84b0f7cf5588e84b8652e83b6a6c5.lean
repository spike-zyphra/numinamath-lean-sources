import Mathlib

open Real

theorem algebra_294504 {x : ℝ} (hx : x = sqrt (7 + sqrt (1 + sqrt (7 + sqrt (1 + sqrt (7 + sqrt (3 + sqrt 1))))))) :
    x = 3 := by 
  have h1 : sqrt 1 = 1 := Real.sqrt_one
  have h2 : sqrt (3 + sqrt 1) = 2 := by 
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : sqrt (7 + sqrt (3 + sqrt 1)) = 3 := by
    rw [h2]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h4 : sqrt (1 + sqrt (7 + sqrt (3 + sqrt 1))) = 2 := by 
    rw [h3]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h5 : sqrt (7 + sqrt (1 + sqrt (7 + sqrt (3 + sqrt 1)))) = 3 := by
    rw [h4]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h6 : sqrt (1 + sqrt (7 + sqrt (1 + sqrt (7 + sqrt (3 + sqrt 1))))) = 2 := by
    rw [h5]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h7 : sqrt (7 + sqrt (1 + sqrt (7 + sqrt (1 + sqrt (7 + sqrt (3 + sqrt 1)))))) = 3 := by
    rw [h6]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [hx]
  exact h7