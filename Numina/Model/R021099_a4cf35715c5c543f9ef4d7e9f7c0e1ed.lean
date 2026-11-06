import Mathlib

theorem algebra_1105 {x : ℝ} (hx : x = 1 / (Real.sqrt 3 - Real.sqrt 2)) : x^6 - 2 * Real.sqrt 2 * x^5 - x^4 + x^3 - 2 * Real.sqrt 3 * x^2 + 2 * x - Real.sqrt 2 = Real.sqrt 3 := by

  have h1 : Real.sqrt 3 > 0 := by
    positivity
  have h2 : Real.sqrt 2 > 0 := by
    positivity
  have h3 : Real.sqrt 3 - Real.sqrt 2 ≠ 0 := by
    have h4 : Real.sqrt 3 > Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have h4 : x = Real.sqrt 3 + Real.sqrt 2 := by
    rw [hx]
    have h5 : Real.sqrt 3 - Real.sqrt 2 ≠ 0 := h3
    field_simp [h5]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - Real.sqrt 2), sq_nonneg (Real.sqrt 3 + Real.sqrt 2)]
  rw [h4]
  have h5 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h7 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [h5]
      _ = 9 := by norm_num
  have h8 : Real.sqrt 2 ^ 4 = 4 := by
    calc
      Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      _ = 2 ^ 2 := by rw [h6]
      _ = 4 := by norm_num
  nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg (Real.sqrt 3 - Real.sqrt 2), sq_nonneg (Real.sqrt 3 + Real.sqrt 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)]