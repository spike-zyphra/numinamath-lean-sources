import Mathlib

theorem inequalities_180192 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 1 / (c ^ 2 + 1) = 2) :
    a * b + b * c + c * a ≤ 3 / 2 := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha
  field_simp [(show a ^ 2 + 1 ≠ 0 by nlinarith), (show b ^ 2 + 1 ≠ 0 by nlinarith), (show c ^ 2 + 1 ≠ 0 by nlinarith)] at h 
  nlinarith [sq_nonneg (a * b - 1 / 2), sq_nonneg (b * c - 1 / 2), sq_nonneg (c * a - 1 / 2), 
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
    mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, 
    mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
    mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
    mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)
  ]