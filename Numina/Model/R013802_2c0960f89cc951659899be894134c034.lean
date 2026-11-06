import Mathlib

theorem inequalities_43241 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a / (1 + a) + b / (1 + b) + c / (1 + c) = 1) :
    a * b * c ≤ 1 / 8 := by

  have h1 : a / (1 + a) + b / (1 + b) + c / (1 + c) = 1 := h

  have h2 : a * (1 + b) * (1 + c) + b * (1 + a) * (1 + c) + c * (1 + a) * (1 + b) = (1 + a) * (1 + b) * (1 + c) := by
    have h1' : a / (1 + a) + b / (1 + b) + c / (1 + c) = 1 := h
    field_simp [(show (1 + a : ℝ) ≠ 0 by linarith), (show (1 + b : ℝ) ≠ 0 by linarith), 
      (show (1 + c : ℝ) ≠ 0 by linarith)] at h1' ⊢
    nlinarith [h1']

  have h3 : a * b + b * c + a * c + 2 * a * b * c = 1 := by
    nlinarith [h2]

  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), 
          sq_nonneg (a * b - 1 / 4), sq_nonneg (a * c - 1 / 4), sq_nonneg (b * c - 1 / 4),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]