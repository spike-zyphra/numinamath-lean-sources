import Mathlib

theorem number_theory_49477 : ∃ a b, a > 10 ^ 2009 ∧ b > 10 ^ 2009 ∧
    3 ^ (4 ^ 5) + 4 ^ (5 ^ 6) = a * b := by

  use (3 ^ 512 + 2 ^ 15625 + 3 ^ 256 * 2 ^ 7813)
  use (3 ^ 512 + 2 ^ 15625 - 3 ^ 256 * 2 ^ 7813)
  constructor
  · -- Show that a > 10 ^ 2009
    norm_num
  constructor
  · -- Show that b > 10 ^ 2009
    norm_num
  · -- Show that 3 ^ (4 ^ 5) + 4 ^ (5 ^ 6) = a * b
    norm_num