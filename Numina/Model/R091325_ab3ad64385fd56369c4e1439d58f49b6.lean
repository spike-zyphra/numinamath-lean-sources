import Mathlib

theorem number_theory_221015 (n : ℕ) (h₀ : n > 0) (h₁ : ∃ k, k < 100 ∧ ∀ i ∈ Finset.range n, (k + i) < 100 ∧ ¬(7 ∈ Nat.digits 10 (k + i))) :
    ∃ x, x > 0 ∧ x.primeFactors.card = 2 ∧ ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p - q = 4 ∧ x = p * q := by

  use 21
  constructor
  · norm_num
  constructor
  · native_decide
  · -- there's two primes p and q, p*q = 21, and p q differ by 4
    use 7, 3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num