import Mathlib

theorem inequalities_124514 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a / (1 + b) + b / (1 + c) + c / (1 + a) = 1) : a * b * c ≤ 1 / 8 := by

  have h1 : 0 < (1 + a) * (1 + b) * (1 + c) := by
    positivity

  have eq1 : a * (1 + c) * (1 + a) + b * (1 + b) * (1 + a) + c * (1 + c) * (1 + b) = (1 + b) * (1 + c) * (1 + a) := by
    field_simp [(show 0 < (1 + b) by positivity), (show 0 < (1 + c) by positivity), 
        (show 0 < (1 + a) by positivity)] at h ⊢
    nlinarith [h]

  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b by positivity) (show 0 < c by positivity)]