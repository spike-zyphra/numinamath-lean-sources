import Mathlib
open Real
theorem inequalities_79176 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
(ha1 : a ≤ √2) (hb1 : b ≤ √2) (hc1 : c ≤ √2) (h : a * b * c = 2) :
√2 * (a * b + 3 * c) / (3 * a * b + c) + √2 * (b * c + 3 * a) / (3 * b * c + a) +√2 * (c * a + 3 * b) / (3 * c * a + b) ≥ a + b + c:= by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha
  have h4 : √2 * (a * b + 3 * c) / (3 * a * b + c) ≥ c := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h5 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)
    nlinarith [ sq_nonneg (c - √2), sq_nonneg (a * b - 1), sq_nonneg (c * a - √2 * a), sq_nonneg (c * b - √2 * b), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith) ]
  have h5 : √2 * (b * c + 3 * a) / (3 * b * c + a) ≥ a := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h6 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)
    nlinarith [ sq_nonneg (a - √2), sq_nonneg (b * c - 1), sq_nonneg (a * b - √2 * b), sq_nonneg (a * c - √2 * c), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith) ]
  have h6 : √2 * (c * a + 3 * b) / (3 * c * a + b) ≥ b := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h7 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)
    nlinarith [ sq_nonneg (b - √2), sq_nonneg (c * a - 1), sq_nonneg (b * c - √2 * c), sq_nonneg (b * a - √2 * a), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith) ]
  linarith only [h4, h5, h6]