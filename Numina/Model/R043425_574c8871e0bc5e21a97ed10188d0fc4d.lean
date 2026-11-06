import Mathlib

open Real
open scoped BigOperators

theorem inequalities_599296 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a^2 / (b + c - a) + b^2 / (c + a - b) + c^2 / (a + b - c) ≥ a + b + c := by
  have pos1 : 0 < b + c - a := by linarith
  have pos2 : 0 < c + a - b := by linarith
  have pos3 : 0 < a + b - c := by linarith
  have h7 : (a^2 / (b + c - a) + b^2 / (c + a - b) + c^2 / (a + b - c)) - (a + b + c) ≥ 0 := by
    have h4 : (a^2 / (b + c - a) + b^2 / (c + a - b) + c^2 / (a + b - c)) - (a + b + c) ≥ 0 := by
      have h8 : a^2 / (b + c - a) + b^2 / (c + a - b) + c^2 / (a + b - c) - (a + b + c) = ( a^2 * (c + a - b) * (a + b - c) + b^2 * (b + c - a) * (a + b - c) + c^2 * (b + c - a) * (c + a - b) - (a + b + c) * (b + c - a) * (c + a - b) * (a + b - c) ) / ((b + c - a) * (c + a - b) * (a + b - c)) := by
        field_simp
        ring
      rw [h8] at *
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
        mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
      ]
      positivity
    linarith
  linarith [h7]