import Mathlib

def triangular_number (n : ℕ) := n * (n + 1) / 2

theorem number_theory_257926 :
    ∃ n m, n > 0 ∧ m > 0 ∧ triangular_number n / triangular_number m = 2 := by
  use 3, 2
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num [triangular_number]