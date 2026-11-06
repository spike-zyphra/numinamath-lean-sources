import Mathlib

open Real
open scoped BigOperators

theorem inequalities_104165 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  3 ≤ a / (b + c - a) + b / (c + a - b) + c / (a + b - c) := by
  have h1 : 0 < b + c - a := by linarith
  have h2 : 0 < c + a - b := by linarith
  have h3 : 0 < a + b - c := by linarith
  have h4 : a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3 ≥ 0 := by
    have pos1 : 0 < (b + c - a) := h1
    have pos2 : 0 < (c + a - b) := h2
    have pos3 : 0 < (a + b - c) := h3
    have h5 : 0 < (b + c - a) * (c + a - b) * (a + b - c) := by
      positivity
    have h6 : a * (c + a - b) * (a + b - c) + b * (b + c - a) * (a + b - c) + c * (b + c - a) * (c + a - b) - 3 * (b + c - a) * (c + a - b) * (a + b - c) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
        mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h7 : a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3 = ( a * (c + a - b) * (a + b - c) + b * (b + c - a) * (a + b - c) + c * (b + c - a) * (c + a - b) - 3 * (b + c - a) * (c + a - b) * (a + b - c) ) / ((b + c - a) * (c + a - b) * (a + b - c)) := by
      field_simp
      ring
    rw [h7] at *
    apply div_nonneg
    linarith
    all_goals
      positivity
  linarith