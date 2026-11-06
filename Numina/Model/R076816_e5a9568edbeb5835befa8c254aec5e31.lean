import Mathlib

def is_perfect_pair (a b : ℕ) := ∃ m, a + b = m^2 ∧ ∃ n, a * b = n^2

theorem number_theory_254642 : ∃ b, is_perfect_pair 122 b := by
  use 122 * 121
  use 122
  constructor
  · -- Show that 122 + (122 * 121) = 122^2
    norm_num
  · -- Show that there exists n such that 122 * (122 * 121) = n^2
    use 122 * 11
    all_goals norm_num