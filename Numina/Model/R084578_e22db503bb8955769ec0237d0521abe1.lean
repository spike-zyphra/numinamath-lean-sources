import Mathlib

theorem number_theory_241054 : ∃ n, ∃ m, n = m + 1 ∧ m > 0 ∧ ∃ k, n / m = k := by
  use 2
  use 1
  constructor
  · norm_num
  constructor
  · norm_num
  · refine ⟨2, by norm_num⟩