import Mathlib

open Real
open scoped BigOperators

theorem inequalities_79706 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  1 ≤ (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ∧
  (a^2 + b^2 + c^2) / (a * b + b * c + c * a) < 2 := by

  have h1 : 0 < a * b + b * c + c * a := by
    positivity

  have h2 : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

  have h3 : 1 ≤ (a^2 + b^2 + c^2) / (a * b + b * c + c * a) := by
    have h4 : a * b + b * c + c * a > 0 := by positivity
    apply (le_div_iff₀ h4).mpr
    linarith [h2]

  have h5 : a^2 + b^2 + c^2 < 2 * (a * b + b * c + c * a) := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      h, h', h'']

  have h6 : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) < 2 := by
    have h7 : a * b + b * c + c * a > 0 := by positivity
    apply (div_lt_iff₀ h7).mpr
    linarith [h5]

  constructor
  · exact h3
  · exact h6