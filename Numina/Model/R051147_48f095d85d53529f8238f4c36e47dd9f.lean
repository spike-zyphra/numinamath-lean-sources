import Mathlib

theorem number_theory_215648 : ∃ n, n > 0 ∧ (n - 1) * 5 + 10 = 1000 := by
  use 199
  constructor
  · norm_num
  · norm_num