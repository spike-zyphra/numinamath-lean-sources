import Mathlib

open Real
open scoped BigOperators

theorem inequalities_51909 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^3 / (b + c - a) + b^3 / (c + a - b) + c^3 / (a + b - c) ≥ a^2 + b^2 + c^2 := by

  have pos1 : 0 < b + c - a := by linarith
  have pos2 : 0 < c + a - b := by linarith
  have pos3 : 0 < a + b - c := by linarith
  
  have h1 : a^3 / (b + c - a) + b^3 / (c + a - b) + c^3 / (a + b - c) - (a^2 + b^2 + c^2) ≥ 0 := by
  
    have h2 : 0 < (b + c - a) * (c + a - b) * (a + b - c) := by positivity
  
    have h3 : a^3 / (b + c - a) + b^3 / (c + a - b) + c^3 / (a + b - c) - (a^2 + b^2 + c^2) =
      ( a^3 * (c + a - b) * (a + b - c) + b^3 * (b + c - a) * (a + b - c) + c^3 * (b + c - a) * (c + a - b) - (a^2 + b^2 + c^2) * (b + c - a) * (c + a - b) * (a + b - c) ) / ( (b + c - a) * (c + a - b) * (a + b - c) ) := by 
      field_simp
      <;> ring
  
    rw [h3] at *
  
    apply div_nonneg
  
    nlinarith [ sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
      sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
      mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
      ]
  
    all_goals positivity
  
  linarith