import Mathlib

theorem algebra_308216 {x : ℝ} (hx : 1 ≤ 2 * x - 1) (h : Real.sqrt (3 * x + 1) = Real.sqrt (2 * x - 1) + 1)
    (h' : 2 * Real.sqrt (x - 1) = Real.sqrt (x + 4) + 1) :
    x = 5 := by

  have h1 : 0 ≤ 3 * x + 1 := by linarith
  have h2 : 0 ≤ 2 * x - 1 := by linarith
  have h3 : 0 ≤ x - 1 := by 
    by_contra h3
    push_neg at h3
    have : Real.sqrt (x - 1) = 0 := by
      rw [Real.sqrt_eq_zero']
      linarith
      all_goals linarith
    rw [this] at h'
    nlinarith [Real.sqrt_nonneg (x + 4), Real.sq_sqrt (show 0 ≤ x + 4 by nlinarith)]
  have h4 : 0 ≤ x + 4 := by nlinarith

  have eq1 : Real.sqrt (3 * x + 1) = Real.sqrt (2 * x - 1) + 1 := h

  have h5 : (Real.sqrt (3 * x + 1)) ^ 2 = (Real.sqrt (2 * x - 1) + 1) ^ 2 := by 
    rw [eq1]

  have h6 : (Real.sqrt (3 * x + 1)) ^ 2 = 3 * x + 1 := Real.sq_sqrt (show 0 ≤ 3 * x + 1 by linarith)
  have h7 : (Real.sqrt (2 * x - 1) + 1) ^ 2 = (Real.sqrt (2 * x - 1)) ^ 2 + 2 * Real.sqrt (2 * x - 1) + 1 := by ring
  rw [h6] at h5
  rw [h7] at h5
  have h8 : (Real.sqrt (2 * x - 1)) ^ 2 = 2 * x - 1 := Real.sq_sqrt (show 0 ≤ 2 * x - 1 by linarith)
  rw [h8] at h5
  have h9 : Real.sqrt (2 * x - 1) = (x + 1) / 2 := by nlinarith
  have h9' : (Real.sqrt (2 * x - 1)) ^ 2 = ((x + 1) / 2) ^ 2 := by rw [h9]
  rw [h8] at h9'
  have h10 : (x - 5) * (x - 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h10) with h11 h12
  · -- x -5 =0
    linarith
  · -- x -1 =0
    have h13 : x = 1 := by linarith
    rw [h13] at h'
    have h14 : Real.sqrt ((1 : ℝ) - 1) = 0 := by
      norm_num [Real.sqrt_eq_zero]
    have h15 : Real.sqrt ((1 : ℝ) + 4) = Real.sqrt (5 : ℝ) := by norm_num
    rw [h14] at h'
    rw [h15] at h'
    nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]