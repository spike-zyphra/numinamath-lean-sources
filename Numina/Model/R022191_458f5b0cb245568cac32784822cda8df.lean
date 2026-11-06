import Mathlib

theorem number_theory_215824 : ∃ m : ℤ, ¬(Int.gcd (100 + m * 101) (101 - m * 100) = 1) := by
  use -201
  norm_num