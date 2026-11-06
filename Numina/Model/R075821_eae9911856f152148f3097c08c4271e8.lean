import Mathlib

theorem number_theory_293047 : ∃ a b c d, a^3 + b^3 + c^3 + d^3 = 100^100 := by
  use 100 ^ 33
  use 2 * 100 ^ 33
  use 3 * 100 ^ 33
  use 4 * 100 ^ 33
  norm_num