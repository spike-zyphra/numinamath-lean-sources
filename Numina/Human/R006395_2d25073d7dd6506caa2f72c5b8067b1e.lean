import Mathlib
/- Let $p$ be a prime number and $k$ be a non-negative integer. Determine the sum of all positive divisors of $p^k$. Show that this sum is equal to $\frac{p^{k+1}-1}{p-1}$. -/
theorem number_theory_636609 (p k : ℕ) (hp : Nat.Prime p) : ∑ d ∈ Nat.divisors (p ^ k), d = (p ^ (k + 1) - 1) / (p - 1):= by
  -- First, prove that p > 1
  have hp1 : p > 1:= by exact Nat.Prime.one_lt hp
  -- Case k = 0: Show that the sum is 1
  by_cases hk : k = 0
  .
    subst k
    simp
    refine Eq.symm (Nat.div_self (by omega))
  -- Case k > 0: Use the formula for the sum of divisors of a power of a prime
  .
    rw [Nat.sum_divisors (by positivity)]
    rw [show (p ^ k).primeFactors = {p} by refine Nat.primeFactors_prime_pow hk hp]
    simp
    rw [show p.factorization p = 1 by exact Nat.Prime.factorization_self hp]
    simp
    -- Use the formula for the sum of a geometric series
    exact Nat.geomSum_eq hp1 (k + 1)
