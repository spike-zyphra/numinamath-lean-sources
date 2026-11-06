import Mathlib

theorem inequalities_598810 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (1 + a) * (1 + b) * (1 + c) ≥ 8 * (1 - a) * (1 - b) * (1 - c) := by 
  have ha1 : a > 0 := by assumption
  have hb1 : b > 0 := by assumption
  have hc1 : c > 0 := by assumption

  have h1 : 1 - a = b + c := by linarith
  have h2 : 1 - b = a + c := by linarith
  have h3 : 1 - c = a + b := by linarith

  rw [h1, h2, h3]

  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]