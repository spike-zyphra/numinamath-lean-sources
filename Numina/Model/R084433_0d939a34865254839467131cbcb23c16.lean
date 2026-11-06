import Mathlib

open Real
open scoped BigOperators

theorem inequalities_263881 (a b : ℤ) :
  a * (a + 1) + b * (b - 1) ≥ 2 * a * b ∧
  (a * (a + 1) + b * (b - 1) = 2 * a * b ↔ a = b ∨ a = b - 1) := by
  constructor
  · nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg ((a - b + 1 : ℤ)), sq_nonneg (a - b - 1 : ℤ), sq_nonneg ((a - b : ℤ) + 1), sq_nonneg (a - b + 1 : ℤ), sq_nonneg (a - (b : ℤ)), sq_nonneg ((a : ℤ) - (b - 1 : ℤ)), sq_nonneg (a - (b - 1 : ℤ))]
  · -- Now, we need to prove the equality conditions
    constructor
    · -- Assume \(a * (a + 1) + b * (b - 1) = 2 * a * b\), prove \(a = b ∨ a = b - 1\)
      intro h
      have h_eq : (a - b) * (a - b + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h_eq) with h1 h2
      · -- Case \(a - b = 0\), so \(a = b\)
        left
        linarith
      · -- Case \(a - b + 1 = 0\), so \(a = b - 1\)
        right
        linarith
    · -- Assume \(a = b ∨ a = b - 1\), prove \(a * (a + 1) + b * (b - 1) = 2 * a * b\)
      rintro (h | h)
      · -- Case \(a = b\)
        rw [h]
        ring
      · -- Case \(a = b - 1\)
        rw [h]
        ring