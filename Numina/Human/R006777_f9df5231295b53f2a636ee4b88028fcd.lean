import Mathlib
/- Let $n$ be an integer such that $n$ is not $0$, $1$, or $2$. Is the number $N = n^2 - (2n-1)$ prime or composite? Show that $N$ is a composite natural number. -/
theorem algebra_641075 (n : ℤ) (hn : n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2) : |n ^ 2 - (2 * n - 1)| > 1 ∧ ¬(Prime (n ^ 2 - (2 * n - 1))):= by
  -- Split the proof into two parts: |N| > 1 and N is not prime
  constructor
  -- First part: Show that |N| > 1
  .
    -- Rewrite N as (n-1)² by algebraic manipulation
    rw [show n ^ 2 - (2 * n - 1) = (n - 1) ^ 2 by ring]
    -- Since (n-1)² is always non-negative, |N| = N
    rw [abs_of_nonneg (by positivity)]
    -- It suffices to show (n-2)*n > 0, which implies (n-1)² > 1
    suffices (n - 2) * n > 0 by linarith
    -- From the constraints n ≠ 0,1,2, we get n ≤ -1 or n ≥ 3
    replace hn : n ≤ -1 ∨ n ≥ 3:= by omega
    -- Consider both cases separately
    rcases hn with hn | hn
    -- In both cases n ≤ -1 and n ≥ 3, we have (n-2)*n > 0
    all_goals
      nlinarith only [hn]
  -- Second part: Show that N is not prime
  .
    -- Since N = (n-1)² is a perfect square with n-1 ≠ ±1, it cannot be prime
    refine IsSquare.not_prime (by use (n - 1) ; ring)
