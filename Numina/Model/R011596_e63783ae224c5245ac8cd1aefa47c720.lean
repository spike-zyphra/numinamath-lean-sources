import Mathlib

theorem number_theory_289621 :
    ∃ a b c d e f : ℤ, [a, b, c, d, e, f].Perm [1, 2, 3, 4, 5, 6] ∧ (a - 1) * (b - 2) * (c - 3) * (d - 4) * (e - 5) * (f - 6) = 75 := by
  use 6, 3, 4, 5, 2, 1
  constructor
  · -- Show that [6, 3, 4, 5, 2, 1] is a permutation of [1, 2, 3, 4, 5, 6]
    native_decide
  · -- Show that the product equals 75
    norm_num