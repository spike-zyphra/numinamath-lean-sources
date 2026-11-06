import Mathlib
/- Let $p$ and $q$ be distinct prime numbers, and let $a$ and $b$ be positive integers. Let $N = p^a q^b$. Prove that Euler's totient function $\varphi(N)$ is equal to $p^{a-1}(p-1)q^{b-1}(q-1)$. -/
theorem number_theory_636734 (p q a b N : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (ha : a > 0) (hb : b > 0) (h1 : p ≠ q) (h2 : N = p ^ a * q ^ b) : Nat.totient N = p ^ (a - 1) * (p - 1) * q ^ (b - 1) * (q - 1):= by
  -- Substitute the definition of N
  subst N
  -- Prove that p and q are coprime using the fact that they are distinct primes
  have h2 : Nat.Coprime p q:= by exact (Nat.coprime_primes hp hq).mpr h1
  -- Extend the coprimality to their powers: p^a and q^b are coprime
  replace h2 : Nat.Coprime (p ^ a) (q ^ b):= by exact Nat.Coprime.pow a b h2
  -- Apply the multiplicative property of Euler's totient function for coprime numbers
  rw [Nat.totient_mul h2]
  -- Calculate totient of p^a using the formula for prime powers
  have h3:= Nat.totient_prime_pow_succ hp (a - 1)
  -- Calculate totient of q^b using the formula for prime powers
  have h4:= Nat.totient_prime_pow_succ hq (b - 1)
  -- Simplify the expression (a-1)+1 = a
  rw [show a - 1 + 1 = a by omega] at h3
  -- Simplify the expression (b-1)+1 = b
  rw [show b - 1 + 1 = b by omega] at h4
  -- Apply the calculated totient values
  rw [h3, h4]
  -- Complete the proof using ring arithmetic
  ring
