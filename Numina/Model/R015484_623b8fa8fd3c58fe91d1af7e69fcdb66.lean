import Mathlib

open Real

theorem inequalities_248084 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a^2 + b^2 = c^2) :
    a + b ≤ √2 * c := by
  have h1 : (a + b) ^ 2 ≤ 2 * (c ^ 2) := by
    nlinarith [sq_nonneg (a - b), h]
  have h2 : (√2 * c) ^ 2 = 2 * (c ^ 2) := by
    calc 
      (√2 * c) ^ 2 = (√2) ^ 2 * c ^ 2 := by ring 
      _ = 2 * c ^ 2 := by norm_num 
  have h3 : (a + b) ^ 2 ≤ (√2 * c) ^ 2 := by
    linarith [h1, h2]
  have h4 : a + b ≥ 0 := by
    linarith
  have h5 : √2 * c ≥ 0 := by
    have h6 : √2 ≥ 0 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith [h6, hc]
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]