import Mathlib

open Real
open scoped BigOperators

theorem inequalities_66885 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  3 ≤ a / (c + a - b) + b / (a + b - c) + c / (b + c - a) := by
  have h1 : 0 < c + a - b := by linarith
  have h2 : 0 < a + b - c := by linarith
  have h3 : 0 < b + c - a := by linarith
  have h4 : a / (c + a - b) + b / (a + b - c) + c / (b + c - a) - 3 ≥ 0 := by
    have h5 : 0 < (c + a - b) * (a + b - c) * (b + c - a) := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h6 : a / (c + a - b) + b / (a + b - c) + c / (b + c - a) - 3 =
        (a * (a + b - c) * (b + c - a) + b * (c + a - b) * (b + c - a) + c * (c + a - b) * (a + b - c) - 3 * (c + a - b) * (a + b - c) * (b + c - a)) / ((c + a - b) * (a + b - c) * (b + c - a)) := by
      field_simp
      ring
    have h7 : a * (a + b - c) * (b + c - a) + b * (c + a - b) * (b + c - a) + c * (c + a - b) * (a + b - c) - 3 * (c + a - b) * (a + b - c) * (b + c - a) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
                mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
                mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
                mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
              ]
    rw [h6] at *
    apply div_nonneg
    linarith
    positivity
  linarith