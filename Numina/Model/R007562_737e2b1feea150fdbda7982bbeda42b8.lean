import Mathlib

theorem number_theory_4997 (k1 k2 : ℤ) :
    ∃ m, (6 * k1 + 5) * (6 * k2 + 5) = 6 * m + 1 := by 
  use 6 * k1 * k2 + 5 * k1 + 5 * k2 + 4
  ring