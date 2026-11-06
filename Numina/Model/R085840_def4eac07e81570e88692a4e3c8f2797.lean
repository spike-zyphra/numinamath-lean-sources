import Mathlib

theorem algebra_119469 {a b : ℝ} (h : a^2 + b^2 - 2 * Real.sqrt 2 * a - 2 * Real.sqrt 3 * b = -5) :
    (2 / a + 3 / b) * (b - a) = 1 := by
  have h1 : (a - Real.sqrt 2) ^ 2 + (b - Real.sqrt 3) ^ 2 = 0 := by 
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
  have ha : a = Real.sqrt 2 := by
    nlinarith [sq_nonneg (a - Real.sqrt 2 : ℝ), sq_nonneg (b - Real.sqrt 3 : ℝ), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
  have hb : b = Real.sqrt 3 := by
    nlinarith [sq_nonneg (a - Real.sqrt 2 : ℝ), sq_nonneg (b - Real.sqrt 3 : ℝ), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
  have ha' : a ≠ 0 := by
    rw [ha]
    have h1 : Real.sqrt 2 > 0 := by positivity
    linarith
  have hb' : b ≠ 0 := by
    rw [hb]
    have h1 : Real.sqrt 3 > 0 := by positivity
    linarith
  rw [ha, hb]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h4 : (2 / Real.sqrt 2 : ℝ) = Real.sqrt 2 := by
    field_simp [show Real.sqrt 2 ≠ 0 by positivity, h2]
    <;> linarith [Real.sqrt_nonneg 2]
  have h5 : (3 / Real.sqrt 3 : ℝ) = Real.sqrt 3 := by
    field_simp [show Real.sqrt 3 ≠ 0 by positivity, h3]
    <;> nlinarith [Real.sqrt_nonneg 3]
  rw [h4, h5]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]