import Mathlib

theorem algebra_326661 (m n : ℝ) (hm : 0 < m) (hn : 0 < n)
    (h : m + 4 * √(m * n) - 2 * √m - 4 * √n + 4 * n = 3) :
    (Real.sqrt m + 2 * Real.sqrt n) / (Real.sqrt m + 2 * Real.sqrt n + 3) = 1 / 2 := by
  have h1 : Real.sqrt (m * n) = Real.sqrt m * Real.sqrt n := by
    rw [Real.sqrt_mul]
    all_goals linarith 
  have h2 : m + 4 * √(m * n) - 2 * √m - 4 * √n + 4 * n = 3 := h
  rw [h1] at h2
  have h3 : (Real.sqrt m + 2 * Real.sqrt n) ^ 2 = m + 4 * (Real.sqrt m * Real.sqrt n) + 4 * n := by 
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ m by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ n by linarith), 
      Real.sqrt_nonneg m, Real.sqrt_nonneg n]
  have h4 : (Real.sqrt m + 2 * Real.sqrt n) ^ 2 - 2 * (Real.sqrt m + 2 * Real.sqrt n) - 3 = 0 := by 
    nlinarith [h2, h3]
  have h5 : (Real.sqrt m + 2 * Real.sqrt n - 3) * (Real.sqrt m + 2 * Real.sqrt n + 1) = 0 := by 
    nlinarith [h4]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case where $\sqrt{m} + 2\sqrt{n} - 3 = 0$
    have h8 : Real.sqrt m + 2 * Real.sqrt n = 3 := by linarith
    rw [h8]
    norm_num
  · -- Case where $\sqrt{m} + 2\sqrt{n} + 1 = 0$
    have h8 : Real.sqrt m + 2 * Real.sqrt n = -1 := by linarith
    have h9 : Real.sqrt m > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    have h10 : Real.sqrt n > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    have h11 : Real.sqrt m + 2 * Real.sqrt n > 0 := by 
      nlinarith [h9, h10]
    linarith [h11, h8]