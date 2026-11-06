import Mathlib

theorem inequalities_114433 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) * (b + c) * (c + a) ≥ 8 * a * b * c := by

  have h1 : (a + b) * (b + c) * (c + a) - 8 * a * b * c = 
    a^2 * b + a^2 * c + a * b^2 + b^2 * c + a * c^2 + b * c^2 - 6 * a * b * c := by
    ring

  have h2 : (a + b) * (b + c) * (c + a) - 8 * a * b * c ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]

  linarith [h1, h2]