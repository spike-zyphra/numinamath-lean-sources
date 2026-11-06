import Mathlib

theorem inequalities_56475 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a + 2 * a * b * c = 1) :
    2 * (a + b + c) + 1 ≥ 32 * a * b * c := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : 2 * (a + b + c) + 1 - 32 * a * b * c ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c - 3 / 2), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  linarith