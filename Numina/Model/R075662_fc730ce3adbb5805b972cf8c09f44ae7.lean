import Mathlib

theorem inequalities_602390 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    a^2 * b^2 + c^2 ≤ 2 ∨ b^2 * c^2 + a^2 ≤ 2 ∨ c^2 * a^2 + b^2 ≤ 2 := by
  by_contra h₁
  push_neg at h₁
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (c^2 - 1),
          sq_nonneg (a*b - 1), sq_nonneg (b*c - 1), sq_nonneg (c*a - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]