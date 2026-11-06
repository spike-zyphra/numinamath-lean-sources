import Mathlib
/- Given that $7,999,999,999$ has at most two prime factors, find its largest prime factor. -/
theorem number_theory_610851 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (h : p * q = 7999999999) : q = 4002001:= by
  -- Rewrite 7,999,999,999 as 1999 * 4002001
  rw [show 7999999999 = 1999 * 4002001 by norm_num] at h
  -- Prove that 1999 is a prime number
  have g1 : Nat.Prime 1999:= by norm_num
  -- Prove that 4002001 is a prime number
  have g2 : Nat.Prime 4002001:= by norm_num
  -- Show that 4002001 divides p * q
  have h1 : 4002001 ∣ p * q:= by rw [h] ; omega
  -- By prime divisibility property, if a prime divides a product, it divides at least one of the factors
  replace h1 : 4002001 ∣ p ∨ 4002001 ∣ q:= by exact (Nat.Prime.dvd_mul g2).mp h1
  -- Consider the two cases: either 4002001 divides p or it divides q
  rcases h1 with h1 | h1
  -- Case 1: 4002001 divides p
  .
    -- If a prime divides another prime, they must be equal (or the divisor is 1)
    replace h1 : 4002001 = 1 ∨ 4002001 = p:= by exact (Nat.dvd_prime hp).mp h1
    -- Simplify the disjunction (1 is not prime, so 4002001 = p)
    simp at h1
    -- Substitute p = 4002001 into the original equation
    rw [←h1] at h
    -- Deduce that q = 1999 from the equation 4002001 * q = 7999999999
    replace h : q = 1999:= by omega
    -- This contradicts p < q since we would have 4002001 < 1999, which is false
    linarith
  -- Case 2: 4002001 divides q
  .
    -- If a prime divides another prime, they must be equal (or the divisor is 1)
    replace h1 : 4002001 = 1 ∨ 4002001 = q:= by exact (Nat.dvd_prime hq).mp h1
    -- Simplify the disjunction (1 is not prime, so 4002001 = q)
    simp at h1
    -- Conclude that q = 4002001, which is our goal
    rw [h1]
