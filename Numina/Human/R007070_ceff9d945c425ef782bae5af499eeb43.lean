import Mathlib

theorem algebra_97984
  {a b : ℝ}
  (h : 1 = (1 / 4) * 2 + a ∧ 2 = (1 / 4) * 1 + b)
  : a + b = 9 / 4 := by

  cases' h with h1 h2

  have a_eq : a = 1/2 := by linarith
  have b_eq : b = 7/4 := by linarith

  rw [a_eq, b_eq]
  ring