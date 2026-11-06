import Mathlib

theorem algebra_244177 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : 1 / a - 1 / b - 1 / (a + b) = 0) :
    (b / a)^3 + (a / b)^3 = 2 * Real.sqrt 5 := by 
  have eq1 : b ^ 2 - a * b - a ^ 2 = 0 := by 
    have h1 : a > 0 := by linarith
    have h2 : b > 0 := by linarith
    have h3 : a + b > 0 := by nlinarith
    field_simp at h
    nlinarith [mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3, mul_pos ha hb]
  have eq2 : b ^ 2 = a * b + a ^ 2 := by 
    nlinarith
  have eq3 : (b / a) ^ 2 - (b / a) - 1 = 0 := by
    have h1 : a > 0 := by linarith
    have : b ^ 2 - a * b - a ^ 2 = 0 := eq1
    field_simp
    nlinarith
  have eq4 : (b / a) = (1 + Real.sqrt 5) / 2 := by
    have h1 : (b / a) ^ 2 - (b / a) - 1 = 0 := eq3
    have h2 : (b / a) > 0 := by
      apply div_pos
      linarith
      linarith
    have h3 : ((b / a) - (1 + Real.sqrt 5) / 2) * ((b / a) - (1 - Real.sqrt 5) / 2) = 0 := by
      nlinarith [h1, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg ((b / a) ^ 2 - (b / a) - 1)]
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Assume $b/a - (1 + \sqrt{5})/2 = 0$, which gives the desired value.
      linarith
    · -- The case $b/a = (1 - \sqrt{5})/2$ leads to a contradiction with positivity.
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg ((b / a) ^ 2 - (b / a) - 1)]
  have eq5 : (b / a) = (1 + Real.sqrt 5) / 2 := eq4
  have eq6 : (a / b) = (Real.sqrt 5 - 1) / 2 := by 
    have eq7 : (a / b) > 0 := by 
      apply div_pos
      linarith
      linarith
    field_simp at *
    nlinarith [eq4, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (a - b)]
  calc 
    (b / a) ^ 3 + (a / b) ^ 3 = ((1 + Real.sqrt 5) / 2) ^ 3 + ((Real.sqrt 5 - 1) / 2) ^ 3 := by
      rw [eq5, eq6]
    _ = (2 + Real.sqrt 5) + (Real.sqrt 5 - 2) := by
      ring_nf
      <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    _ = 2 * Real.sqrt 5 := by
      ring_nf
      <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]