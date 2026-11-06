import Mathlib

theorem algebra_7416 (a b : ℝ) (h : -a < b ∧ b < a) : |2*a+b|+|2*a-b| = 4*a := by
  have h1 : -a < b := h.1
  have h2 : b < a := h.2
  have ha : 0 < a := by linarith 
  have h3 : 2 * a + b > 0 := by linarith 
  have h4 : 2 * a - b > 0 := by linarith
  rw [abs_of_pos h3, abs_of_pos h4]
  linarith