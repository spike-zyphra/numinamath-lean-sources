import Mathlib

open Real
open scoped BigOperators

theorem inequalities_102534 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
  (hc : 0 < c) (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a / (1 + a) + b / (1 + b) > c / (1 + c) := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h3 : 0 < 1 + c := by linarith
  have h4 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
  have h5 : a / (1 + a) + b / (1 + b) - c / (1 + c) > 0 := by
    have h6 : (a / (1 + a) + b / (1 + b) - c / (1 + c)) = (a * (1 + b) * (1 + c) + b * (1 + a) * (1 + c) - c * (1 + a) * (1 + b)) / ((1 + a) * (1 + b) * (1 + c)) := by
      field_simp [h1, h2, h3]
      ring
    rw [h6]
    have h7 : a * (1 + b) * (1 + c) + b * (1 + a) * (1 + c) - c * (1 + a) * (1 + b) > 0 := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - b), sq_nonneg (b - c),
       sq_nonneg (c - a), mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
        ]
    apply div_pos
    linarith
    all_goals positivity
  linarith [h5]