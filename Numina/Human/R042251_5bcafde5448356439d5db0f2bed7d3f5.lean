import Mathlib

/- Let $ a,b,c$ be positive real numbers such that $ a^3 \plus{} b^3 \equal{} c^3$.Prove that:

$ a^2 \plus{} b^2 \minus{} c^2 > 6(c \minus{} a)(c \minus{} b)$. -/
theorem inequalities_52700 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^3 + b^3 = c^3) :
    a^2 + b^2 - c^2 > 6 * (c - a) * (c - b) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), h, mul_pos ha hb, mul_pos hb hc,
    mul_pos ha hc, sq_nonneg (a + b - c)]