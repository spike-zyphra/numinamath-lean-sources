import Mathlib

theorem algebra_4611
  {a b : ℝ}
  (h : a * (a - 2) - (a ^ 2 - 2 * b) = 2018) :
  (a ^ 2 + b ^ 2) / 2 - a * b = 509040.5 := by
  have eq1 : b = a + 1009 := by
    linarith
  rw [eq1]
  ring_nf
  <;> linarith