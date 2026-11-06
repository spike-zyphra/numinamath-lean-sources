import Mathlib

open Polynomial

theorem algebra_151 {a b : ℝ} (ha : (X^2 + C (-3) * X + C 1 : ℝ[X]).eval a = 0)
    (hb : (X^2 + C (-3) * X + C 1 : ℝ[X]).eval b = 0) (hab : a ≠ b) :
    a^2 * b + a * b^2 = 3 := by
  have h1 : a^2 - 3 * a + 1 = 0 := by 
    simpa using ha
  have h2 : b^2 - 3 * b + 1 = 0 := by 
    simpa using hb
  have h3 : a + b = 3 := by
    have h4 : a^2 - b^2 = 3 * (a - b) := by
      nlinarith
    have h5 : a + b = 3 := by 
      apply (mul_right_inj' (sub_ne_zero.mpr hab)).mp
      linarith
    exact h5
  have h6 : a * b = 1 := by
    nlinarith [h1, h2, h3]
  have h7 : a^2 * b + a * b^2 = (a * b) * (a + b) := by 
    ring
  rw [h7, h6, h3]
  all_goals norm_num