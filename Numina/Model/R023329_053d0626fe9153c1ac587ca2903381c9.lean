import Mathlib

theorem algebra_179769 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + 4 * y^2 = 12 * x * y) :
    Real.logb 10 (x + 2 * y) - 2 * Real.logb 10 2 =
    (Real.logb 10 x + Real.logb 10 y) / 2 := by
  have h1 : 0 < x + 2 * y := by nlinarith
  have h4 : Real.logb 10 4 = 2 * Real.logb 10 2 := by
    calc
      Real.logb 10 4 = Real.logb 10 (2 ^ 2) := by norm_num
      _ = 2 * Real.logb 10 2 := by simp [Real.logb_pow]

  have h2 : Real.logb 10 (x + 2 * y) - 2 * Real.logb 10 2 = Real.logb 10 ((x + 2 * y) / 4) := by
    have h3 : Real.logb 10 ((x + 2 * y) / 4) = Real.logb 10 (x + 2 * y) - Real.logb 10 4 := by
      rw [Real.logb_div (by nlinarith) (by norm_num)]
    rw [h4] at h3
    linarith
  have h3 : (Real.logb 10 x + Real.logb 10 y) / 2 = Real.logb 10 ((x * y) ^ (1 / 2 : ℝ)) := by
    have h4 : Real.logb 10 ((x * y) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.logb 10 (x * y) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals nlinarith [show x * y > 0 by positivity]
    have h5 : Real.logb 10 (x * y) = Real.logb 10 x + Real.logb 10 y := by
      rw [Real.logb_mul (by positivity) (by positivity)]
    rw [h5] at h4
    linarith
  rw [h2, h3]
  have h4 : (x * y) ^ (1 / 2 : ℝ) = Real.sqrt (x * y) := by
    rw [Real.sqrt_eq_rpow]
  have h5 : (x + 2 * y) / 4 = Real.sqrt (x * y) := by
    have h6 : (x + 2 * y) ^ 2 = 16 * (x * y) := by
      nlinarith [h, mul_pos hx hy]
    have h7 : ((x + 2 * y) / 4) ^ 2 = x * y := by
      nlinarith [h6]
    have h8 : 0 ≤ (x + 2 * y) / 4 := by
      nlinarith
    have h9 : Real.sqrt (((x + 2 * y) / 4) ^ 2) = Real.sqrt (x * y) := by
      rw [show ((x + 2 * y) / 4) ^ 2 = x * y by nlinarith [h7]]
    have h10 : Real.sqrt (((x + 2 * y) / 4) ^ 2) = (x + 2 * y) / 4 := by
      rw [Real.sqrt_sq (show 0 ≤ (x + 2 * y) / 4 by linarith)]
    have h11 : (x + 2 * y) / 4 = Real.sqrt (x * y) := by
      linarith [h10, h9]
    linarith
  rw [h4] at *
  rw [h5]
  all_goals norm_num
  all_goals linarith