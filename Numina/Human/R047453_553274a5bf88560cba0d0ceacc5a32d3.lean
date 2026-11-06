import Mathlib

theorem number_theory_318744 : ∃ n : ℕ, n > 0 ∧ (29^n) % 1000 = 1 := by
  use 100
  constructor
  · norm_num -- This proves that 100 > 0
  · norm_num [Nat.pow_mod] -- This computes (29 ^ 100) % 1000 = 1