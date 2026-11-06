import Mathlib
/- The number

$$
316990099009901=\frac{32016000000000001}{101}
$$

is the product of two distinct prime numbers. Compute the smaller of these two primes. -/
theorem number_theory_610585 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : 316990099009901 = p * q) (hpq : p < q) : p = 4002001:= by
  -- First, we establish that 316990099009901 = 79207901 * 4002001
  have h1 : 316990099009901 = 79207901 * 4002001:= by omega
  -- Verify that 79207901 is prime
  have g1 : Nat.Prime 79207901:= by norm_num
  -- Verify that 4002001 is prime
  have g2 : Nat.Prime 4002001:= by norm_num
  -- Since p is a factor of p*q, p divides 316990099009901
  have h2 : p ∣ 316990099009901:= by rw [h] ; simp
  -- Substitute our factorization into the divisibility statement
  rw [h1] at h2
  -- By prime divisibility property, if p divides a product, it divides at least one of the factors
  replace h2 : p ∣ 79207901 ∨ p ∣ 4002001:= by exact (Nat.Prime.dvd_mul hp).mp h2
  -- Consider the two possible cases
  rcases h2 with h2 | h2
  -- Case 1: p divides 79207901
  .
    -- If p divides 79207901, then p must equal either 1 or 79207901 (since 79207901 is prime)
    replace h2 : p = 1 ∨ p = 79207901:= by exact (Nat.dvd_prime g1).mp h2
    rcases h2 with h2 | h2
    -- Subcase 1.1: p = 1
    .
      -- Reach a contradiction since p is prime and cannot equal 1
      by_contra _
      -- A prime number is greater than 1
      have hp1 : p > 1:= by exact Nat.Prime.one_lt hp
      linarith
    -- Subcase 1.2: p = 79207901
    .
      -- Reach a contradiction since p < q but this would make q = 4002001, which is smaller than 79207901
      by_contra _
      subst p
      -- If p = 79207901, then q must be 4002001 to satisfy the product
      replace h : q = 4002001:= by omega
      linarith
  -- Case 2: p divides 4002001
  .
    -- If p divides 4002001, then p must equal either 1 or 4002001 (since 4002001 is prime)
    replace h2 : p = 1 ∨ p = 4002001:= by exact (Nat.dvd_prime g2).mp h2
    rcases h2 with h2 | h2
    -- Subcase 2.1: p = 1
    .
      -- Reach a contradiction since p is prime and cannot equal 1
      by_contra _
      have hp1 : p > 1:= by exact Nat.Prime.one_lt hp
      linarith
    -- Subcase 2.2: p = 4002001
    .
      -- This is our answer: p = 4002001
      exact h2
