import Mathlib

theorem algebra_15833 (x : ℝ) (hx : x ≥ 0) : x^2 = -4 * x ↔ x = 0 := by
  constructor
  · -- Assume x^2 = -4 * x, then x = 0
    intro h
    have h1 : x * (x + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case x = 0
      linarith
    · -- Case x + 4 = 0
      nlinarith
  · -- Assume x = 0, then x^2 = -4 * x
    intro h
    rw [h]
    norm_num