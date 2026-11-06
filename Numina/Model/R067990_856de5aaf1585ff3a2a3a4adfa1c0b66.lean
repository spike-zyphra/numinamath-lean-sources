import Mathlib

theorem number_theory_107771 : ∃ x y : ℕ, x ^ 2 + y ^ 2 = 2018 ^ 2021 := by 
  use 13 * 2018 ^ 1010, 43 * 2018 ^ 1010
  norm_num