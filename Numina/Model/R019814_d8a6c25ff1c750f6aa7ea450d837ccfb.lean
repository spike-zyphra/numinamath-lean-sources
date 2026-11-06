import Mathlib

theorem number_theory_190545 (n : ℕ) (a b c : ℕ) (h₀ : n = a^2 + b^2 + c^2) :
    ∃ x y z, n^2 = x^2 + y^2 + z^2 := by
  use n, 0, 0
  all_goals
    simp