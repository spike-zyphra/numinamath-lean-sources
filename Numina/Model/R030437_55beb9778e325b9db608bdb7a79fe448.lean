import Mathlib

theorem number_theory_87610 (n : ℕ) (hn : 3 ≤ n) (h : ∃ k, k^2 = 1 + 3 * n) :
    ∃ a b c, ∃ m, m^2 = 1 + (3 * n + 3) / (a^2 + b^2 + c^2) := by
  use 0, 0, 0
  use 1
  all_goals
    simp