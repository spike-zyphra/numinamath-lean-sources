import Mathlib

def f (n : ℕ) := 15 * n

theorem number_theory_121378 : ∃ m, f m = 2016 ∨ (f m > 2016 ∧ f (m - 1) < 2016) := by
  use 135
  norm_num [f]
  <;> norm_num [f]