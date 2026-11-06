import Mathlib

theorem inequalities_308247 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    2 + Real.sqrt 5 < Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) := by
  have h9 : Real.sqrt (4 * a + 1) > 1 := by
    have h3 : 4 * a > 0 := by nlinarith
    have h4 : 4 * a + 1 > 1 := by nlinarith
    have h5 : Real.sqrt (4 * a + 1) > Real.sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have h6 : Real.sqrt 1 = 1 := Real.sqrt_one
    linarith [h5, h6]

  have h10 : Real.sqrt (4 * b + 1) > 1 := by
    have h3 : 4 * b > 0 := by nlinarith
    have h4 : 4 * b + 1 > 1 := by nlinarith
    have h5 : Real.sqrt (4 * b + 1) > Real.sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have h6 : Real.sqrt 1 = 1 := Real.sqrt_one
    linarith [h5, h6]

  have h11 : Real.sqrt (4 * c + 1) > 1 := by
    have h3 : 4 * c > 0 := by nlinarith
    have h4 : 4 * c + 1 > 1 := by nlinarith
    have h5 : Real.sqrt (4 * c + 1) > Real.sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have h6 : Real.sqrt 1 = 1 := Real.sqrt_one
    linarith [h5, h6]

  have h14 : Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) > 2 + Real.sqrt 5 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), sq_nonneg (Real.sqrt (4 * a + 1) - Real.sqrt (4 * b + 1)), sq_nonneg (Real.sqrt (4 * b + 1) - Real.sqrt (4 * c + 1)), sq_nonneg (Real.sqrt (4 * a + 1) - Real.sqrt (4 * c + 1)), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 1 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * b + 1 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * c + 1 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, h, Real.sqrt_nonneg 5]
  exact h14
  all_goals nlinarith