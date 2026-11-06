import Mathlib

theorem algebra_115617 {a b : ℝ} (ha : a ≥ 2014) (hb : b ≥ -2014)
    (h : Real.sqrt 3 * Real.sqrt (a - 2014) + Real.sqrt (b + 2014) - 2 - (a + b) / 2 = 0) :
    a = 2017 ∧ b = -2013 := by
  have h1 : Real.sqrt (a - 2014) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h2 : Real.sqrt (b + 2014) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h3 : (Real.sqrt (a - 2014)) ^ 2 = a - 2014 := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : (Real.sqrt (b + 2014)) ^ 2 = b + 2014 := by
    rw [Real.sq_sqrt]
    linarith

  have h5 : a = 2017 := by
    nlinarith [sq_nonneg (Real.sqrt (a - 2014) - Real.sqrt 3), sq_nonneg (Real.sqrt (b + 2014) - 1), Real.sqrt_nonneg (a - 2014), Real.sqrt_nonneg (b + 2014), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (a - 2014 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (b + 2014 : ℝ) by linarith), h, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (a - 2014)), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (b + 2014)), mul_nonneg (Real.sqrt_nonneg (a - 2014)) (Real.sqrt_nonneg (b + 2014))]
  have h6 : b = -2013 := by
    nlinarith [sq_nonneg (Real.sqrt (a - 2014) - Real.sqrt 3), sq_nonneg (Real.sqrt (b + 2014) - 1), Real.sqrt_nonneg (a - 2014), Real.sqrt_nonneg (b + 2014), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (a - 2014 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (b + 2014 : ℝ) by linarith), h, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (a - 2014)), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (b + 2014)), mul_nonneg (Real.sqrt_nonneg (a - 2014)) (Real.sqrt_nonneg (b + 2014))]
  exact ⟨h5, h6⟩