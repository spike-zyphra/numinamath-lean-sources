import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_54461 {p q : ℝ} (hp : p < q) (h : p^2 + q^2 = 2 * p * q) :
    ∫ x in (p)..q, max (1 - x^2 - (1 - p^2)) 0 = 7 / 3 := by
  have h1 : (p - q) ^ 2 = 0 := by
    linarith
  have h2 : p - q = 0 := by
    rw [sq_eq_zero_iff] at h1
    linarith
  have h3 : p = q := by linarith
  linarith