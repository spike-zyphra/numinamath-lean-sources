import Mathlib

/- Let $p$ be a prime number and $k$ be a natural number. Determine the number of positive divisors of $p^k$. Show that this number is equal to $k+1$. -/
theorem number_theory_637939 (p k : ℕ) (hp : p.Prime):
    (p ^ k).divisors.card = k + 1 := by
    rw [Nat.divisors_prime_pow hp]
    simp
