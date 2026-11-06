import Mathlib

theorem number_theory_258227 (a : ℕ → ℕ) (ha : ∀ n, ∑ d in n.divisors, a d = 2 ^ n) :
    ∀ n, n ∣ a n := by
  have h1 := ha 0
  simp at h1
  all_goals 
    linarith