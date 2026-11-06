import Mathlib
/- Let $p, q, r$ be distinct prime numbers and let $N = pqr$. Determine the number of positive integers $a$ strictly less than $N$ that share no common prime factors with $N$. Show that this number is equal to $(p-1)(q-1)(r-1)$. -/
theorem number_theory_642262 (p q r : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) (h1 : p ≠ q) (h2 : p ≠ r) (h3 : q ≠ r) : (Finset.filter (p * q * r).Coprime (Finset.range (p * q * r))).card = (p - 1) * (q - 1) * (r - 1):= by
  -- Convert the problem to use the totient function
  rw [←Nat.totient_eq_card_coprime (p * q * r)]

  -- Prove that p*q is coprime to r using the fact that they are distinct primes
  have g1 : Nat.Coprime (p * q) r:= by
    have g1 : Nat.Coprime p r:= by exact (Nat.coprime_primes hp hr).mpr h2
    have g2 : Nat.Coprime q r:= by exact (Nat.coprime_primes hq hr).mpr h3
    exact Nat.Coprime.mul g1 g2

  -- Apply the multiplicative property of totient function for (p*q)*r
  rw [Nat.totient_mul g1]

  -- Prove that p is coprime to q using the fact that they are distinct primes
  have g2 : Nat.Coprime p q:= by exact (Nat.coprime_primes hp hq).mpr h1

  -- Apply the multiplicative property of totient function for p*q
  rw [Nat.totient_mul g2]

  -- Apply the totient formula for prime numbers p, q, and r
  rw [Nat.totient_prime hp]
  rw [Nat.totient_prime hq]
  rw [Nat.totient_prime hr]
