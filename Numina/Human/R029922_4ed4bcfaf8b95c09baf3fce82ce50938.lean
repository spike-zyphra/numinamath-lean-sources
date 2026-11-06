import Mathlib

/- Theorem 6.2 states that if \( p \) is a prime number, then the Euler's totient function \( \phi(p) \) equals \( p-1 \). Conversely, if \( p \) is a positive integer such that \( \phi(p) = p-1 \), then \( p \) must be a prime number.-/
theorem number_theory_4858 :
    ∀ {p : ℕ}, 0 < p → (Nat.totient p = p - 1 ↔ Nat.Prime p) :=
  --The problem is exactly the proposition Nat.totient_eq_iff_prime in Mathlib.
  Nat.totient_eq_iff_prime
