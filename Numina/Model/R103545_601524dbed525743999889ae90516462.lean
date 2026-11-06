import Mathlib

theorem number_theory_183720 (m n p q : ℤ) (hmpq : m ≠ p) :
    m - p ∣ m * q + n * p ↔ m - p ∣ m * n + p * q := by
  constructor
  · -- Assume m-p divides m*q + n*p, prove m-p divides m*n + p*q
    intro h
    have eq : (m * n + p * q) = (m * q + n * p) + (m - p) * (n - q) := by
      ring
    rw [eq]
    apply dvd_add
    exact h
    apply dvd_mul_right
  · -- Assume m-p divides m*n + p*q, prove m-p divides m*q +n*p
    intro h
    have eq : (m * q + n * p) = (m * n + p * q) - (m - p) * (n - q) := by
      ring
    rw [eq]
    apply dvd_sub
    exact h
    apply dvd_mul_right