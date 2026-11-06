import Mathlib


theorem inequalities_114740 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + a * c = 3) :
    3 / 2 ≤ a ^ 2 / (1 + b * c) + b ^ 2 / (1 + c * a) + c ^ 2 / (1 + a * b) := by
  have h1 : a + b + c ≥ 3 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h2 : a ^ 2 / (1 + b * c) + b ^ 2 / (1 + c * a) + c ^ 2 / (1 + a * b) - 3 / 2 ≥ 0 := by
    have h3 : 0 < (1 + b * c) * (1 + c * a) * (1 + a * b) := by positivity
    have h4 : a ^ 2 / (1 + b * c) + b ^ 2 / (1 + c * a) + c ^ 2 / (1 + a * b) - 3 / 2 =
        (2 * (a^2 * (1 + c * a) * (1 + a * b) + b^2 * (1 + b * c) * (1 + a * b) + c^2 * (1 + b * c) * (1 + c * a)) - 3 * (1 + b * c) * (1 + c * a) * (1 + a * b)) / (2 * (1 + b * c) * (1 + c * a) * (1 + a * b)) := by
      field_simp
      ring
    rw [h4]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1), 
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      h, h1, mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
      mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)]
    all_goals positivity
  linarith