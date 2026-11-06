import Mathlib

theorem number_theory_211124 (a : ℕ → ℕ → ℕ)
    (ha : ∀ n m, a n m = a (n - 1) (m - 1) + 1) :
    ∀ n, ∑ i in Finset.range (n + 1), a n i = (a n (n / 2)) ^ 2 := by
  -- Show inconsistency of the recurrence relation at n=0, m=0
  have h1 := ha 0 0
  norm_num at h1 
  all_goals 
    omega