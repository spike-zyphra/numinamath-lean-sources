import Mathlib

open BigOperators

/- Theorem 6.5 states that if \( n = p_{1}^{a_{1}} p_{2}^{a_{2}} \cdots p_{k}^{a_{k}} \) is the prime-power factorization of a positive integer \( n \), then the Euler's totient function \( \phi(n) \) can be expressed as:
\[
\phi(n) = n \left(1 - \frac{1}{p_{1}}\right) \left(1 - \frac{1}{p_{2}}\right) \cdots \left(1 - \frac{1}{p_{k}}\right).
\]-/
theorem number_theory_4861 : ∀ (n : ℕ), ↑(Nat.totient n) =
    ↑n * ∏ p in n.primeFactors, (1 - (p : ℚ)⁻¹) :=
  --The problem is exactly the proposition Nat.totient_eq_mul_prod_factors in Mathlib.
  Nat.totient_eq_mul_prod_factors
