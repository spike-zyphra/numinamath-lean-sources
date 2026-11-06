import Mathlib


theorem number_theory_138433: ∃ n a b c d e f g: ℕ, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧ f < g ∧
  a + b + c + d + e + f + g = 2 * n ∧ e + f + g ≤ n := by
  use 46, 10, 11, 12, 13, 14, 15, 17
  all_goals norm_num