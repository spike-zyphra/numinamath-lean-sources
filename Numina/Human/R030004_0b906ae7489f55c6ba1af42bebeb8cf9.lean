import Mathlib

/- Theorem 6.4 states that if \( m \) and \( n \) are relatively prime positive integers, then the Euler's totient function satisfies the equation \( \phi(m n) = \phi(m) \phi(n) \).-/
theorem number_theory_4860 : ∀ {m n : ℕ}, Nat.Coprime m n →
    Nat.totient (m * n) = Nat.totient m * Nat.totient n :=
  --The problem is exactly the proposition Nat.totient_mul in Mathlib.
  Nat.totient_mul
