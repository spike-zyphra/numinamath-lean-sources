import Mathlib

theorem number_theory_283696 (n : ℕ) (h : n > 0) (h' : ∃ k, n = 3 * k ∧ n + 15 = 3 * (k + 1)) :
    n = 150 := by 
  rcases h' with ⟨k, hn, h1⟩
  omega