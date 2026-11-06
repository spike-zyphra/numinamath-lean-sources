import Mathlib

theorem Other_5820 (a : ℕ → ℕ) (adef : ∀ n, ∑ d in n.divisors, a d = 2^n) :
  ∀ n, n ∣ a n := by 
  intro n
  have h1 := adef 0
  have h2 := adef 1
  simp [Finset.sum_singleton] at h1 h2 
  all_goals omega