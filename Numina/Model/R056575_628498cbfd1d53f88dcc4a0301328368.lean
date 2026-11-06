import Mathlib

theorem algebra_143945 (x y : ℕ) :
    7^(x + y) = 7^(x + 2) * 7^(2 * x + 1) ↔ y = 2 * x + 3 := by 
  constructor
  · -- Forward implication: equating the exponents gives the relationship between y and x
    intro h
    have h1 : 7 ^ (x + 2) * 7 ^ (2 * x + 1) = 7 ^ (3 * x + 3) := by
      ring_nf
    rw [h1] at h
    have h2 : x + y = 3 * x + 3 := by
      exact Nat.pow_right_injective (by norm_num) h
    omega
  · -- Forward implication: assuming y = 2x + 3 proving the equation
    intro h
    rw [h]
    have h1 : 7 ^ (x + (2 * x + 3)) = 7 ^ (3 * x + 3) := by
      ring_nf
    have h2 : 7 ^ (x + 2) * 7 ^ (2 * x + 1) = 7 ^ (3 * x + 3) := by
      ring_nf
    rw [h1, h2]