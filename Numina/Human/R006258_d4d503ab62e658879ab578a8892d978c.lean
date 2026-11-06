import Mathlib

/- Theorem: Let $p$ and $q$ be distinct prime numbers, and let $a$ and $b$ be positive integers. If $n = p^a q^b$, then Euler's totient function $\phi(n)$ is equal to $p^{a-1}(p-1)q^{b-1}(q-1)$. -/
theorem number_theory_635205 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : n = p ^ a * q ^ b) :
    n.totient = p ^ (a - 1) * (p - 1) * q ^ (b - 1) * (q - 1) := by
  -- We use the fact that φ(ab) = φ(a)φ(b) if a and b are coprime. Since p ≠ q, p ^ a and q ^ b are coprime.
  -- We also use the fact that φ(p^n) = p ^ (n - 1) * (p - 1) for any prime p and positive integer n.
  rw [hn, Nat.totient_mul (Nat.Coprime.pow a b ((Nat.coprime_primes hp hq).mpr hpq)), Nat.totient_prime_pow hp ha, Nat.totient_prime_pow hq hb]
  ring