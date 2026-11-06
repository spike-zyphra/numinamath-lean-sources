import Mathlib

theorem inequalities_121982 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a / (1 + a) + b / (1 + b) + c / (1 + c) = 1) :
    a * b * c ≤ 1 / 8 := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h3 : 0 < 1 + c := by linarith

  have eq1 : a / (1 + a) + b / (1 + b) + c / (1 + c) = 1 := h
  have eq2 : a * (1 + b) * (1 + c) + b * (1 + a) * (1 + c) + c * (1 + a) * (1 + b) = (1 + a) * (1 + b) * (1 + c) := by
    field_simp [(show 1 + a ≠ 0 by linarith), (show 1 + b ≠ 0 by linarith), (show 1 + c ≠ 0 by linarith)] at eq1 ⊢
    nlinarith [h]
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
            sq_nonneg (a * b - 1 / 4), sq_nonneg (b * c - 1 / 4), sq_nonneg (a * c - 1 / 4),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]