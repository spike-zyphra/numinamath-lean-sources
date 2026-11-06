import Mathlib

open Real

theorem inequalities_597418 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a ^ 2 + b ^ 2 + c ^ 2 + 2 * sqrt (3 * a * b * c) ≤ 1 := by
  have h1 : 0 < 3 * a * b * c := by
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    have hc' : 0 < c := hc
    positivity
  have h2 : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a) := by
    ring
  have h3 : a ^ 2 + b ^ 2 + c ^ 2 = 1 - 2 * (a * b + b * c + c * a) := by
    rw [h] at h2
    linarith
  have h4 : a * b + b * c + c * a > 0 := by
    nlinarith
  have h5 : 0 ≤ 1 - (a ^ 2 + b ^ 2 + c ^ 2) := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h6 : 2 * sqrt (3 * a * b * c) ≤ 1 - (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h7 : 0 ≤ (1 - (a ^ 2 + b ^ 2 + c ^ 2) : ℝ) := h5
    have h8 : sqrt (3 * a * b * c) ≥ 0 := by positivity
    have h9 : sqrt (3 * a * b * c) ^ 2 = 3 * a * b * c := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith [sq_nonneg (sqrt (3 * a * b * c) - (1 - (a ^ 2 + b ^ 2 + c ^ 2)) / 2), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      Real.sqrt_nonneg (3 * a * b * c), Real.sq_sqrt (show (0 : ℝ) ≤ 3 * a * b * c by positivity), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_nonneg (Real.sqrt_nonneg (3 * a * b * c)) (Real.sqrt_nonneg (3 * a * b * c)), 
      sq_nonneg ((1 - (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2 - 12 * (3 * a * b * c)), 
      h7
    ]
  linarith [h3, h6]