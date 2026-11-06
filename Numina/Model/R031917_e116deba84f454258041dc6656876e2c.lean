import Mathlib


theorem number_theory_294199 :
    ∃ a d : ℕ, a > 0 ∧ d ≠ 0 ∧ ∃ k : ℕ, a * (a + d) * (a + 2 * d) * (a + 3 * d) * (a + 4 * d) =
      k ^ 2008 := by 
  use 120 ^ 803, 120 ^ 803
  constructor
  · -- Show a > 0
    norm_num
  constructor
  · -- Show d ≠ 0
    norm_num
  use 120 ^ 2
  norm_num