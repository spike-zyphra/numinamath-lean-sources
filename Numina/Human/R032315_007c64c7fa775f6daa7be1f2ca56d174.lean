import Mathlib

open Real

theorem inequalities_45542 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    sqrt a + sqrt b + sqrt c ≥ a * b + b * c + c * a := by
  have h1 : sqrt a ≥ a * (3 - a) / 2 := by
    have h1 : 0 ≤ a := by linarith
    have h2 : a ≤ 3 := by nlinarith [sq_nonneg (a - 3), h]
    have h3 : sqrt a ≥ 0 := Real.sqrt_nonneg a
    have h4 : 2 * sqrt a ≥ a * (3 - a) := by
      nlinarith [sq_nonneg (sqrt a - (a * (3 - a) / 2)), Real.sq_sqrt (show 0 ≤ a by linarith),
        sq_nonneg (a - 1), sq_nonneg (a - 2), sq_nonneg (a - 3)]
    linarith
  have h2 : sqrt b ≥ b * (3 - b) / 2 := by
    have h1 : 0 ≤ b := by linarith
    have h2 : b ≤ 3 := by nlinarith [sq_nonneg (b - 3), h]
    have h3 : sqrt b ≥ 0 := Real.sqrt_nonneg b
    have h4 : 2 * sqrt b ≥ b * (3 - b) := by
      nlinarith [sq_nonneg (sqrt b - (b * (3 - b) / 2)), Real.sq_sqrt (show 0 ≤ b by linarith),
        sq_nonneg (b - 1), sq_nonneg (b - 2), sq_nonneg (b - 3)]
    linarith
  have h3 : sqrt c ≥ c * (3 - c) / 2 := by
    have h1 : 0 ≤ c := by linarith
    have h2 : c ≤ 3 := by nlinarith [sq_nonneg (c - 3), h]
    have h3 : sqrt c ≥ 0 := Real.sqrt_nonneg c
    have h4 : 2 * sqrt c ≥ c * (3 - c) := by
      nlinarith [sq_nonneg (sqrt c - (c * (3 - c) / 2)), Real.sq_sqrt (show 0 ≤ c by linarith),
        sq_nonneg (c - 1), sq_nonneg (c - 2), sq_nonneg (c - 3)]
    linarith
  have h4 : sqrt a + sqrt b + sqrt c ≥ a * b + b * c + c * a := by
    have h4 : a * b + b * c + c * a ≤ (9 - (a^2 + b^2 + c^2)) / 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    nlinarith [h1, h2, h3, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  linarith [h4]