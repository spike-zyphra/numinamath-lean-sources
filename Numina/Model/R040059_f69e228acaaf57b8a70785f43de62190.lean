import Mathlib

open Real
open scoped BigOperators

theorem inequalities_603807 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  (c - a) / (b + c - a) + (a - b) / (c + a - b) + (b - c) / (a + b - c) ≤ 0 := by
  have hb' : 0 < b + c - a := by linarith
  have hc' : 0 < c + a - b := by linarith
  have ha' : 0 < a + b - c := by linarith
  have h3 : (c - a) / (b + c - a) + (a - b) / (c + a - b) + (b - c) / (a + b - c) =
      ( (c - a) * (c + a - b) * (a + b - c) + (a - b) * (b + c - a) * (a + b - c) + (b - c) * (b + c - a) * (c + a - b) ) / ( (b + c - a) * (c + a - b) * (a + b - c) ) := by
    field_simp
    <;> ring
  rw [h3] at *
  apply div_nonpos_of_nonpos_of_nonneg
  · -- Show that the total numerator is non-positive
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
        mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
    ]
  · -- Show that denominator ≥ 0
    positivity