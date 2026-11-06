import Mathlib

theorem inequalities_276858 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 * (b + c) + a * (b^2 + c^2 - b * c) > 0 := by 
  have h1 : a ^ 2 * (b + c) > 0 := by
    positivity
  have h2 : a * (b ^ 2 + c ^ 2 - b * c) > 0 := by
    have h3 : b ^ 2 + c ^ 2 - b * c > 0 := by 
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), mul_pos hb hc, sq_pos_of_pos hb, sq_pos_of_pos hc]
    apply mul_pos
    linarith
    linarith
  linarith [h1, h2]