import Mathlib

open Real

theorem algebra_1651 {x : ℝ} (hx : x = √(10 + 8 * √(3 + 2 * √2))) : x = 4 + √2 := by
  have h1 : √(3 + 2 * √2) = √2 + 1 := by
    have h2 : (√2 + 1) ^ 2 = 3 + 2 * √2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [←h2]
    field_simp
    <;> norm_num [Real.sqrt_nonneg]
    all_goals linarith [Real.sqrt_nonneg (2 : ℝ)]
  rw [hx]
  have h2 : √(10 + 8 * √(3 + 2 * √2)) = 4 + Real.sqrt 2 := by
    have h3 : √(3 + 2 * √2) = √2 + 1 := h1
    have h4 : (10 + 8 * √(3 + 2 * √2)) = (18 + 8 * √2) := by
      rw [h3]
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h4]
    have h5 : (4 + Real.sqrt 2) ^ 2 = 18 + 8 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (√2 - 4)]
    have h7 : 0 ≤ (4 + Real.sqrt 2 : ℝ) := by
      positivity
    rw [show √(18 + 8 * Real.sqrt 2) = √((4 + Real.sqrt 2) ^ 2) by rw [h5] ]
    rw [Real.sqrt_sq (h7)]
    <;> positivity
  linarith [h2]