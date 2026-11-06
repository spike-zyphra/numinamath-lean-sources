import Mathlib

theorem algebra_159342 (n : ℕ) (hn : n = 100) (r : ℝ) (hr : r = 0.2) :
    r * √(n - 2) / √(1 - r ^ 2) > 1.99 := by
  have h1 : (n : ℝ) = 100 := by
    rw [hn]
    all_goals norm_num
  have h2 : (n - 2 : ℝ) = 98 := by
    rw [h1]
    all_goals norm_num
  have h4 : (1 - r ^ 2 : ℝ) = 0.96 := by
    rw [hr]
    all_goals norm_num
  have h5 : r * √(n - 2) / √(1 - r ^ 2) = (0.2 * √98) / √0.96 := by
    rw [h2, h4, hr]
    all_goals norm_num
  rw [h5]
  have h9 : (0.2 * Real.sqrt 98) / Real.sqrt (0.96 : ℝ) > 1.99 := by
    have h11 : Real.sqrt (0.96 : ℝ) > 0 := by
      apply Real.sqrt_pos.mpr
      norm_num
    have h12 : Real.sqrt (98 : ℝ) > 0 := by
      apply Real.sqrt_pos.mpr
      norm_num
    have h13 : 0.2 * Real.sqrt (98 : ℝ) > 1.99 * Real.sqrt (0.96 : ℝ) := by
      have h15 : (0.2 * Real.sqrt (98 : ℝ)) ^ 2 > (1.99 * Real.sqrt (0.96 : ℝ)) ^ 2 := by
        have h16 : (0.2 * Real.sqrt (98 : ℝ)) ^ 2 = 0.2 ^ 2 * (Real.sqrt (98 : ℝ) ^ 2) := by ring
        have h17 : Real.sqrt (98 : ℝ) ^ 2 = 98 := Real.sq_sqrt (by norm_num)
        have h18 : (1.99 * Real.sqrt (0.96 : ℝ)) ^ 2 = 1.99 ^ 2 * (Real.sqrt (0.96 : ℝ) ^ 2) := by ring
        have h19 : Real.sqrt (0.96 : ℝ) ^ 2 = 0.96 := Real.sq_sqrt (by norm_num)
        rw [h16, h17, h18, h19]
        norm_num
      have h20 : 0.2 * Real.sqrt (98 : ℝ) ≥ 0 := by positivity
      have h21 : 1.99 * Real.sqrt (0.96 : ℝ) ≥ 0 := by positivity
      nlinarith [h15, Real.sqrt_nonneg (98 : ℝ), Real.sqrt_nonneg (0.96 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (98 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (0.96 : ℝ) by norm_num) ]
    have h15 : (0.2 * Real.sqrt 98) / Real.sqrt (0.96 : ℝ) > 1.99 := by
      apply (lt_div_iff₀ (by positivity)).mpr
      linarith
    linarith
  linarith [h9]