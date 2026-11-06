import Mathlib

theorem inequalities_120423 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a * b + b * c + c * a ≤ 1 / 2 := by
  have h1 : (a + b + c) ^ 2 = 1 := by
    rw [h]
    norm_num
  have h2 : a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) = 1 := by
    have h1' : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
      ring
    nlinarith [h1']
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    h2, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
  ]