import Mathlib

theorem inequalities_600604 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a / (1 + a) + b / (1 + b) + c / (1 + c) = 1) :
    a + b + c ≥ 3 / 2 := by
  have h1 : a * (1 + b) * (1 + c) + b * (1 + a) * (1 + c) + c * (1 + a) * (1 + b) = (1 + a) * (1 + b) * (1 + c) := by
    have h1 : a * (1 + b) * (1 + c) + b * (1 + a) * (1 + c) + c * (1 + a) * (1 + b) = (1 + a) * (1 + b) * (1 + c) := by
      field_simp [(show 1 + a ≠ 0 by linarith), (show 1 + b ≠ 0 by linarith), (show 1 + c ≠ 0 by linarith)] at h ⊢
      nlinarith [h]
    linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]