import Mathlib

theorem inequalities_156893 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (h : a * b = x ^ 2) :
    (a + x) * (b + x) ≥ 4 * x ^ 2 := by 
  have h1 : (a + b) ^ 2 ≥ 4 * x ^ 2 := by
    nlinarith [sq_nonneg (a - b), h, mul_pos ha hb]

  have h2 : a + b ≥ 2 * x := by
    nlinarith [sq_nonneg (a + b - 2 * x), h1, mul_pos ha hb, mul_pos ha hx, mul_pos hb hx]

  -- We can compute (a + x)(b + x) by expanding it
  -- $(a + x)(b + x) = ab + ax + bx + x^2$
  nlinarith [sq_nonneg (a * b - x^2), h2, h, mul_pos ha hb, mul_pos ha hx, mul_pos hb hx, sq_nonneg (a - b)]