import Mathlib

open Real

theorem inequalities_142505 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    sqrt 3 ≤ a + b + c := by
  have h1 : (a + b + c) ^ 2 ≥ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h2 : sqrt 3 ≤ a + b + c := by
    have h3 : (sqrt 3) ^ 2 = 3 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h4 : (sqrt 3) ^ 2 ≤ (a + b + c) ^ 2 := by
      linarith [h3, h1]
    have h5 : 0 ≤ sqrt 3 := Real.sqrt_nonneg 3
    have h6 : 0 ≤ a + b + c := by linarith [ha, hb, hc]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  exact h2