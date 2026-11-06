import Mathlib

open Real
open scoped BigOperators

theorem inequalities_312430 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (h : a^2 + b^2 = c^2) :
  (a^3 + b^3 + c^3) / (a * b * c) ≥ 2 + sqrt 2 := by 
  have h1 : 0 < a * b * c := by
    positivity
  have h3 : a^3 + b^3 + c^3 ≥ (2 + Real.sqrt 2) * (a * b * c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a * c - b * c), sq_nonneg (a * c + b * c), 
      sq_nonneg (a + b - c), sq_nonneg (a * b), sq_nonneg (a^2 + b^2 - c^2), sq_nonneg (c^2 - 2 * a * b), 
      sq_nonneg (a * c - b * c), sq_nonneg (a - b), sq_nonneg (c^2 - 2 * a^2), sq_nonneg (c^2 - 2 * b^2), 
      Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
      sq_nonneg (c - a * Real.sqrt 2), sq_nonneg (c - b * Real.sqrt 2), 
      Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  have h4 : (a^3 + b^3 + c^3) / (a * b * c) ≥ 2 + Real.sqrt 2 := by 
    have h4' : a * b * c > 0 := h1
    apply (le_div_iff₀ h4').mpr 
    linarith [h3]
  linarith [h4]