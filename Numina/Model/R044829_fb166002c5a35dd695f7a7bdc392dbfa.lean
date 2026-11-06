import Mathlib

theorem algebra_160258 (x : ℝ) (hx : x = Real.sqrt 3 / 2) :
    (1 + Real.sqrt (1 + x)) / (x + 1) + (1 + Real.sqrt (1 - x)) / (x - 1) = -2 - 4 * Real.sqrt 3 := by

  have h1 : 1 + x = (2 + Real.sqrt 3) / 2 := by 
    rw [hx]
    ring

  have h2 : 1 - x = (2 - Real.sqrt 3) / 2 := by
    rw [hx]
    ring

  have h3 : Real.sqrt (1 + x) = (Real.sqrt 3 + 1) / 2 := by
    rw [h1]
    have h4 : Real.sqrt ((2 + Real.sqrt 3) / 2) = (Real.sqrt 3 + 1) / 2 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by nlinarith), sq_nonneg (Real.sqrt 3 - 1)]
    exact h4

  have h5 : Real.sqrt (1 - x) = (Real.sqrt 3 - 1) / 2 := by 
    rw [h2]
    have h6 : Real.sqrt ((2 - Real.sqrt 3) / 2) = (Real.sqrt 3 - 1) / 2 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by nlinarith), sq_nonneg (Real.sqrt 3 - 1)]
    exact h6

  have h6 : x + 1 = (Real.sqrt 3 + 2) / 2 := by 
    rw [hx]
    ring

  have h7 : x - 1 = (Real.sqrt 3 - 2) / 2 := by 
    rw [hx]
    ring

  rw [h3, h6, h5, h7]
  field_simp [(show Real.sqrt 3 ^ 2 = 3 by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]), (show (Real.sqrt 3 + 2 : ℝ) ≠ 0 by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]), (show (Real.sqrt 3 - 2 : ℝ) ≠ 0 by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)])]
  <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 3 - 1), sq_nonneg (Real.sqrt 3 + 1)]