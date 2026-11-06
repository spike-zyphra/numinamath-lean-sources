import Mathlib

theorem number_theory_38453 :
    ∃ n : ℕ, 0 < n ∧ (1994 * 1993 ^ n) % 10000 = 1994 := by
  use 500
  constructor
  . norm_num
  . norm_num