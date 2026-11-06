import Mathlib

theorem number_theory_229885 :
    ∃ n : ℤ, IsSquare (2 * n + 1) ∧ IsSquare (3 * n + 1) ∧ 40 ∣ n := by 
  use 0
  constructor
  · -- Show that 2 * 0 + 1 is a square
    use 1
    norm_num 
  constructor
  · -- Show that 3 * 0 + 1 is a square
    use 1
    norm_num 
  · -- Show that 40 divides 0
    norm_num