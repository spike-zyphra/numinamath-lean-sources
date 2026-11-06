import Mathlib

open Real
open scoped BigOperators

theorem inequalities_47155 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  ¬∃ x : ℝ, b^2 * x^2 + (b^2 + c^2 - a^2) * x + c^2 = 0 := by
  intro h1
  rcases h1 with ⟨x, hx⟩
  have h2 : (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 - 4 * (b ^ 2) * (c ^ 2) < 0 := by
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
      mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
    ]
  have h3 : (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 - 4 * (b ^ 2) * (c ^ 2) ≥ 0 := by
    nlinarith [sq_nonneg (b^2 * x + (b^2 + c^2 - a^2) / 2), sq_nonneg (b^2 * x + (b^2 + c^2 - a^2) / 2 - (b^2 * x + (b^2 + c^2 - a^2) / 2)), sq_nonneg (b * x + c), sq_nonneg (b * x - c), sq_nonneg (a - b - c), sq_nonneg (a + b - c), sq_nonneg (a - (b + c)), sq_nonneg (a - (b - c)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  linarith