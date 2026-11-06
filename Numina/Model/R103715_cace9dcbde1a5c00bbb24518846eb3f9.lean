import Mathlib

open Real

theorem algebra_300591 {x y : ℝ}
    (hx : x = (sqrt 3 + sqrt 2) / (sqrt 3 - sqrt 2))
    (hy : y = (sqrt 3 - sqrt 2) / (sqrt 3 + sqrt 2)) :
    x^2 + x * y + y^2 + 1 = 100 := by
  have h1 : sqrt 3 - sqrt 2 ≠ 0 := by 
    have h2 : sqrt 3 > sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h3 : sqrt 3 - sqrt 2 > 0 := sub_pos_of_lt h2
    linarith
  have h4 : sqrt 3 + sqrt 2 ≠ 0 := by 
    have h5 : sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (3 : ℝ))
    have h6 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (2 : ℝ))
    have h7 : sqrt 3 + sqrt 2 > 0 := add_pos h5 h6
    linarith
  have hxy : x * y = 1 := by 
    rw [hx, hy]
    field_simp [h1, h4]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h9 : x + y = 10 := by
    rw [hx, hy]
    have h8 : (sqrt 3 + sqrt 2) / (sqrt 3 - sqrt 2) + (sqrt 3 - sqrt 2) / (sqrt 3 + sqrt 2) = 10 := by 
      have h10 : (sqrt 3 - sqrt 2) ≠ 0 := h1
      have h11 : (sqrt 3 + sqrt 2) ≠ 0 := h4
      field_simp [h10, h11]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        sq_pos_of_pos (show 0 < (sqrt 3 : ℝ) by positivity), sq_pos_of_pos (show 0 < (sqrt 2 : ℝ) by positivity)]
    linarith [h8]
  have h2 : x^2 + x * y + y^2 + 1 = (x + y)^2 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), hxy]
  rw [h2, h9]
  norm_num