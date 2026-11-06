import Mathlib

theorem inequalities_599893 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c = 1) : (a - 1) * (b - 1) * (c - 1) ≥ 8 := by
  have h1 : a * b * c = a * b + a * c + b * c := by 
    field_simp at h
    nlinarith
  
  have h2 : (a - 1) * (b - 1) * (c - 1) = (a + b + c) - 1 := by
    nlinarith [h1]

  have h3 : a + b + c ≥ 9 := by 
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 3), sq_nonneg (c - 3),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)]

  linarith [h2, h3]