import Mathlib

theorem algebra_118059 (x : ℝ) (hx : x = Real.sqrt 3 + Real.sqrt 2) :
    2 * x ^ 5 + x ^ 4 - 20 * x ^ 3 - 10 * x ^ 2 + 2 * x + 1 = 0 := by
  rw [hx]
  have h1 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    have h31 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt (3 * 2 : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
    have h32 : Real.sqrt (3 * 2 : ℝ) = Real.sqrt (6 : ℝ) := by
      norm_num
    rw [h31, h32]
  have h4 : Real.sqrt 3 ^ 2 = 3 := by
    rw [Real.sq_sqrt]
    all_goals linarith
  have h5 : Real.sqrt 2 ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    all_goals linarith
  have h7 : (Real.sqrt 3 + Real.sqrt 2) ^ 2 = 5 + 2 * Real.sqrt 6 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, h1, h2, h3, Real.sqrt_nonneg (6 : ℝ)]
  have h8 : (Real.sqrt 3 + Real.sqrt 2)^3 = 9 * Real.sqrt 3 + 11 * Real.sqrt 2 := by
    calc
      (Real.sqrt 3 + Real.sqrt 2) ^ 3 = (Real.sqrt 3 + Real.sqrt 2) * (Real.sqrt 3 + Real.sqrt 2) ^ 2 := by ring
      _ = (Real.sqrt 3 + Real.sqrt 2) * (5 + 2 * Real.sqrt 6) := by rw [h7]
      _ = 9 * Real.sqrt 3 + 11 * Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h1, h2, h3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, h4, h5, Real.sqrt_nonneg (6 : ℝ)]
  have h9 : (Real.sqrt 3 + Real.sqrt 2)^4 = 49 + 20 * Real.sqrt 6 := by
    calc
      (Real.sqrt 3 + Real.sqrt 2) ^ 4 = (Real.sqrt 3 + Real.sqrt 2) * (Real.sqrt 3 + Real.sqrt 2) ^ 3 := by ring
      _ = (Real.sqrt 3 + Real.sqrt 2) * (9 * Real.sqrt 3 + 11 * Real.sqrt 2) := by rw [h8]
      _ = 49 + 20 * Real.sqrt 6 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h1, h2, h3, h4, h5, Real.sqrt_nonneg 6, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg (6 : ℝ)]
  have h10 : (Real.sqrt 3 + Real.sqrt 2)^5 = 89 * Real.sqrt 3 + 109 * Real.sqrt 2 := by
    calc
      (Real.sqrt 3 + Real.sqrt 2) ^ 5 = (Real.sqrt 3 + Real.sqrt 2) * (Real.sqrt 3 + Real.sqrt 2) ^ 4 := by ring
      _ = (Real.sqrt 3 + Real.sqrt 2) * (49 + 20 * Real.sqrt 6) := by rw [h9]
      _ = 89 * Real.sqrt 3 + 109 * Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h1, h2, h3, h4, h5, Real.sqrt_nonneg 6, Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg (6 : ℝ)]
  nlinarith [h7, h8, h9, h10, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h1, h2, h3, h4, h5, Real.sqrt_nonneg (6 : ℝ)]