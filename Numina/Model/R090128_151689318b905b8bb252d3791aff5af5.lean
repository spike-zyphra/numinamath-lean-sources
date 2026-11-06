import Mathlib

theorem algebra_113843 (f : Polynomial ℤ) (hf : f = X^5 + X + 1) :
    ∃ g h : Polynomial ℤ, f = g * h ∧ g = X^2 + X + 1 ∧ h = X^3 - X^2 + 1 := by
  use X^2 + X + 1, X^3 - X^2 + 1
  constructor
  · -- Verify that f = g * h
    rw [hf]
    ring_nf
  constructor
  · -- Verify that g = X^2 + X + 1
    rfl
  · -- Verify that h = X^3 - X^2 + 1
    rfl