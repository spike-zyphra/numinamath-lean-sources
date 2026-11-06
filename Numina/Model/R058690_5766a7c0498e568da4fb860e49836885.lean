import Mathlib

theorem algebra_7988 {x y : ℝ} (hx : x = Real.sqrt 2) (hy : y = Real.sqrt 3) :
    ((x + y) * (x - y))^2 / (x + y)^2 + 2 * x * y = 5 := by
  rw [hx, hy]
  have h1 : ((Real.sqrt 2 + Real.sqrt 3) * (Real.sqrt 2 - Real.sqrt 3))^2 / (Real.sqrt 2 + Real.sqrt 3)^2 + 2 * Real.sqrt 2 * Real.sqrt 3 = (Real.sqrt 2)^2 + (Real.sqrt 3)^2 := by
    have h2 : (Real.sqrt 2 + Real.sqrt 3) ≠ 0 := by
      have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
      have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
    have h3 : (Real.sqrt 2 + Real.sqrt 3) * (Real.sqrt 2 - Real.sqrt 3) = -1 := by
      calc 
        (Real.sqrt 2 + Real.sqrt 3) * (Real.sqrt 2 - Real.sqrt 3) = (Real.sqrt 2)^2 - (Real.sqrt 3)^2 := by ring
        _ = 2 - 3 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        _ = -1 := by norm_num
    have h4 : ((Real.sqrt 2 + Real.sqrt 3) * (Real.sqrt 2 - Real.sqrt 3))^2 = 1 := by
      rw [h3]
      norm_num 
    have h5 : (Real.sqrt 2 + Real.sqrt 3)^2 ≠ 0 := by
      have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
      have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    -- Now simplify the original expression.
    field_simp [h5, h3]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h7 : (Real.sqrt 2 : ℝ)^2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  have h8 : (Real.sqrt 3 : ℝ)^2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  linarith [h1, h7, h8]