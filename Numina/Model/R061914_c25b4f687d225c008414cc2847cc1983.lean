import Mathlib

theorem number_theory_306171 : ∃ n, (n - 1) * (2 * n - 1) < 2010 ∧ 2010 < n * (2 * n - 1) := by
  use 32
  norm_num