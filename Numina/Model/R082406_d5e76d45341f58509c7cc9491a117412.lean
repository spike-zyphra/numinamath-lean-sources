import Mathlib

theorem algebra_120910 (m : ℤ) :
    ∃ x : ℤ, x^3 - m * x^2 + m * x - (m ^ 2 + 1) = 0 ↔ m = 0 ∨ m = -3 := by
  use m + 1
  constructor
  · -- Assume h and prove m =0 ∨ m=-3
    intro h
    have h1 : m * (m + 3) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.1 h1) with h2 h3
    · left
      linarith
    · right 
      linarith
  · -- Assume m=0 ∨ m=-3, prove h
    rintro (h | h)
    · -- Assume m =0
      rw [h]
      nlinarith
    · -- Assume m=-3
      rw [h]
      nlinarith