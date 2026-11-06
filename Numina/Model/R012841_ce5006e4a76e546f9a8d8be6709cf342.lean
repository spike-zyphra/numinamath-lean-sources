import Mathlib

open Real
open scoped BigOperators

theorem inequalities_280847 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  3 < (a^2 + 2 * b * c) / (b^2 + c^2) + (b^2 + 2 * a * c) / (c^2 + a^2) +
    (c^2 + 2 * a * b) / (a^2 + b^2) := by

  have h1 : 0 < b ^ 2 + c ^ 2 := by nlinarith [hb, hc]
  have h2 : 0 < c ^ 2 + a ^ 2 := by nlinarith [hc, ha]
  have h3 : 0 < a ^ 2 + b ^ 2 := by nlinarith [ha, hb]

  have h4 : a ^ 2 + 2 * b * c > b ^ 2 + c ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      sq_nonneg (a - (b - c)), sq_nonneg (b - (a - c)), sq_nonneg (c - (a - b)), 
      h, h', h'']

  have h5 : b ^ 2 + 2 * a * c > c ^ 2 + a ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      sq_nonneg (b - (a - c)), sq_nonneg (a - (b - c)), sq_nonneg (c - (a - b)), 
      h, h', h'']

  have h6 : c ^ 2 + 2 * a * b > a ^ 2 + b ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      sq_nonneg (c - (a - b)), sq_nonneg (a - (b - c)), sq_nonneg (b - (a - c)), 
      h, h', h'']

  have h7 : (a ^ 2 + 2 * b * c) / (b ^ 2 + c ^ 2) > 1 := by
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith

  have h8 : (b ^ 2 + 2 * a * c) / (c ^ 2 + a ^ 2) > 1 := by
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith

  have h9 : (c ^ 2 + 2 * a * b) / (a ^ 2 + b ^ 2) > 1 := by 
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith

  linarith [h7, h8, h9]