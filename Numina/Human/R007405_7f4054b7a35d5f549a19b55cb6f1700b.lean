import Mathlib

/- Show that any odd number can be written as the difference between two perfect squares. -/
theorem number_theory_66595 (n : ℤ) (h₀ : Odd n) :
    ∃ a b, n = a^2 - b^2 := by 
  -- Express n as $2k + 1$, where it is given n is odd
  cases' h₀ with k hk; use k + 1, k
  -- Rewrite using $k+1$ and $k$
  rw [hk]; ring