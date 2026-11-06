import Mathlib

theorem number_theory_115547 : ∃ x y : ℕ, x ^ 2 - 119 * y ^ 2 = 1 := by 
  use 120, 11
  all_goals
    norm_num
    <;> omega