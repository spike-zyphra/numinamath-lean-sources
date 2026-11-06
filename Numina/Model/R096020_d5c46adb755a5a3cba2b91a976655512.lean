import Mathlib

theorem number_theory_115519 : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 2 * x * y * z := by 
  use 0, 0, 0
  all_goals norm_num