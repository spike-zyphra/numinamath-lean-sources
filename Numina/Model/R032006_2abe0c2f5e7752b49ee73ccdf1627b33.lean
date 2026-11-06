import Mathlib

open Real
open scoped BigOperators

theorem calculus_22293 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : 2*a^2 + 4*b^2 + c^2 = 4*a*b + 2*a*c) :
  cos (arccos ((a^2 + c^2 - b^2)/(2*a*c))) = 7/8 := by
  have h1 : (c - 2*b)^2 = 0 := by
    nlinarith [sq_nonneg (a - 2*b), sq_nonneg (c - 2*b), sq_nonneg (2*b - c), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h2 : c = 2*b := by
    nlinarith
  have h3 : (a - 2*b)^2 = 0 := by
    rw [show c = 2*b by linarith [h2] ] at h
    nlinarith [sq_nonneg (a - 2*b), sq_nonneg (b - a/2), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h4 : a = 2*b := by
    nlinarith
  have h5 : (a^2 + c^2 - b^2)/(2*a*c) = 7/8 := by
    rw [show a = 2*b by linarith [h4], show c = 2*b by linarith [h2]]
    field_simp
    <;> nlinarith
  rw [h5]
  exact Real.cos_arccos (by norm_num) (by norm_num)