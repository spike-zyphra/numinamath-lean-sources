import Mathlib
/- Let $k$ be a non-negative integer. Let $N = 2^4 \cdot 3^5 \cdot 4^6 \cdot 6^k$. How many natural-number factors does $N$ have? Show the answer is $(k+17)(k+6)$. -/
theorem algebra_637746 (N k : ℕ) (hN : N = 2 ^ 4 * 3 ^ 5 * 4 ^ 6 * 6 ^ k) : N.divisors.card = (k + 17) * (k + 6):= by
  -- Rewrite 6^k as 2^k * 3^k since 6 = 2 * 3
  rw [show 6 ^ k = 2 ^ k * 3 ^ k by rw [show 6 = 2 * 3 by simp] ; exact Nat.mul_pow 2 3 k] at hN
  -- Simplify the expression to collect powers of 2 and 3: 2^4 * 3^5 * 4^6 * 2^k * 3^k = 2^(k+16) * 3^(k+5)
  rw [show 2 ^ 4 * 3 ^ 5 * 4 ^ 6 * (2 ^ k * 3 ^ k) = 2 ^ (k + 16) * 3 ^ (k + 5) by ring_nf] at hN
  -- Substitute the simplified form into N
  subst N
  -- Prove that 2^(k+16) and 3^(k+5) are coprime (since 2 and 3 are different primes)
  have h1 : Nat.Coprime (2 ^ (k + 16)) (3 ^ (k + 5)):= by exact Nat.Coprime.pow (k + 16) (k + 5) rfl
  -- Use the fact that for coprime numbers, divisors of the product equal product of divisors
  rw [Nat.Coprime.card_divisors_mul h1]
  -- General lemma: for prime p, the number of divisors of p^(k+1) is k+2
  have h2 : ∀ p k : ℕ, Nat.Prime p → (p ^ (k + 1)).divisors.card = k + 2:= by
    intro p k hp
    rw [Nat.card_divisors]
    rw [show Nat.primeFactors (p ^ (k + 1)) = {p} by refine Nat.primeFactors_prime_pow (by omega) hp]
    simp
    exact Nat.Prime.factorization_self hp
    have hp : p > 1:= by exact Nat.Prime.one_lt hp
    positivity
  -- Apply the lemma to 2^(k+16): it has k+17 divisors
  have h3:= h2 2 (k + 15) (by norm_num)
  -- Apply the lemma to 3^(k+5): it has k+6 divisors
  have h4:= h2 3 (k + 4) (by norm_num)
  -- Adjust the exponents to match our case
  rw [show k + 15 + 1 = k + 16 by ring] at h3
  rw [show k + 4 + 1 = k + 5 by ring] at h4
  -- Combine the results: total divisors = (k+17) * (k+6)
  rw [h3, h4]
