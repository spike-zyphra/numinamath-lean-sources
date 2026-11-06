import Mathlib

theorem inequalities_3296 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = a + b + c + 6) :
    a * b + b * c + c * a ≤ 2 * (a + b + c) ∧ 2 * (a + b + c) ≤ a^2 + b^2 + c^2 := by
  constructor
  · -- Prove $a \cdot b + b \cdot c + c \cdot a \le 2 \cdot (a + b + c)$.
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  · -- Prove $2 \cdot (a + b + c) \le a^2 + b^2 + c^2$.
    nlinarith [h, sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]