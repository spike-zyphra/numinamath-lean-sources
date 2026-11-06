import Mathlib

theorem number_theory_157698 (p : ℕ) :
    ∃ x y : ℚ, x ^ 2 - y ^ 2 * p = 1 := by
  use 1, 0
  norm_num
  <;> all_goals norm_num