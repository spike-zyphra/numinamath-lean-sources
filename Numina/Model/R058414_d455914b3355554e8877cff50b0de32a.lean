import Mathlib

theorem algebra_220416 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 1 / (a + b) = 1 / a + 1 / b) (k : ℝ) (hk : 0 < k) :
    1 / a = 2 ∧ 1 / b = 2 := by
  have h1 : 0 < a + b := by linarith
  have eq1 : a * b = (a + b) ^ 2 := by 
    have denom_ne_zero : a + b ≠ 0 := by linarith
    field_simp [denom_ne_zero, show a ≠ 0 by linarith, show b ≠ 0 by linarith] at h
    nlinarith [h]
  have eq2 : a ^ 2 + a * b + b ^ 2 = 0 := by
    nlinarith [eq1]
  have h2 : a ^ 2 + a * b + b ^ 2 > 0 := by 
    nlinarith [mul_pos ha hb, sq_pos_of_pos ha, sq_pos_of_pos hb]
  linarith