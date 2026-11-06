import Mathlib

theorem inequalities_123796 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (a - a * b ≤ 1 / 4 ∨ b - b * c ≤ 1 / 4 ∨ c - c * a ≤ 1 / 4) ∧
    (a - a * b ≥ 2 / 9 ∨ b - b * c ≥ 2 / 9 ∨ c - c * a ≥ 2 / 9) := by
  constructor
  · -- First part: show that among a - a * b, b - b * c, c - c * a, there is one which is at most 1 / 4.
    by_contra h₁
    push_neg at h₁
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  · -- Second part: show that among a - a * b, b - b * c, c - c * a, there is one which is at least 2 / 9.
    by_contra h₂
    push_neg at h₂
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]