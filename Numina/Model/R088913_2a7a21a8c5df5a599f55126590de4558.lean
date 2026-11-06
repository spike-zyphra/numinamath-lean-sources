import Mathlib

theorem number_theory_101577 (n : ℕ) (hn : n > 0) :
    ∃ k, k^2 = 2^n + 3 ↔ False := by 
  use 0
  simp
  all_goals
    omega