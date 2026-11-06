import Mathlib

/- Lemma 6.1. Let \( p \) be a prime number and \( a \) a positive integer. Then
\[
\sigma\left(p^{a}\right) = \left(1 + p + p^{2} + \cdots + p^{a}\right) = \frac{p^{a+1} - 1}{p - 1}
\]-/
theorem number_theory_4892_1 (p a : ℕ) [hp : Fact (Nat.Prime p)] (_ : 0 < a) :
    (Finset.sum (Nat.divisors (p ^ a)) fun x => x) =
    Finset.sum (Finset.range (a + 1)) fun x => p ^ x := by
  --The problem is exactly the proposition Nat.sum_divisors_prime_pow in Mathlib.
  apply Nat.sum_divisors_prime_pow; exact hp.1

/- Lemma 6.1. Let \( p \) be a prime number and \( a \) a positive integer. Then
\[
\tau\left(p^{a}\right) = a + 1
\]-/
theorem number_theory_4892_2 (p a : ℕ) [hp : Fact (Nat.Prime p)] (_ : 0 < a) :
    Fintype.card (Nat.divisors (p ^ a)) = a + 1 := by
  --The problem is exactly the proposition Nat.divisors_prime_pow in Mathlib.
  rw [Nat.divisors_prime_pow hp.1 a]; simp
