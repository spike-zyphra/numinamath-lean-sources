import Mathlib

theorem inequalities_618378 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≤ 1) :
    a / (1 - a) + b / (1 - b) + c / (1 - c) ≥ 3 * (a + b + c) / (3 - (a + b + c)) := by
  have h1 : 0 < 1 - a := by
    nlinarith
  have h2 : 0 < 1 - b := by
    nlinarith
  have h3 : 0 < 1 - c := by
    nlinarith
  have h4 : 0 < 3 - (a + b + c) := by
    nlinarith
  have h5 : a / (1 - a) + b / (1 - b) + c / (1 - c) - 3 * (a + b + c) / (3 - (a + b + c)) ≥ 0 := by
    have h6 : 0 < (1 - a) * (1 - b) * (1 - c) * (3 - (a + b + c)) := by
      positivity
    have h7 : a / (1 - a) + b / (1 - b) + c / (1 - c) - 3 * (a + b + c) / (3 - (a + b + c)) =
        (a * (1 - b) * (1 - c) * (3 - (a + b + c)) + b * (1 - a) * (1 - c) * (3 - (a + b + c)) + c * (1 - a) * (1 - b) * (3 - (a + b + c)) - 3 * (a + b + c) * (1 - a) * (1 - b) * (1 - c)) / ((1 - a) * (1 - b) * (1 - c) * (3 - (a + b + c))) := by
      field_simp [(show (1 - (a : ℝ)) ≠ 0 by nlinarith), (show (1 - (b : ℝ)) ≠ 0 by nlinarith), (show (1 - (c : ℝ)) ≠ 0 by nlinarith), (show 3 - (a + b + c : ℝ) ≠ 0 by nlinarith)]
      ring
    rw [h7] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    all_goals positivity
  linarith