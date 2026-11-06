import Mathlib

theorem number_theory_205078 : ∃ n : ℕ, n > 0 ∧ n < 2006 ∧ (2006 * n) % (2006 + n) = 0 := by
  use 1475
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num