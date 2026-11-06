import Mathlib

theorem algebra_221385 (x : ℝ) (hx : x > 0) : x^2 + 6 * x = 91 ↔ x = 7 := by
  constructor
  · -- Forward direction: Assume x^2 + 6 * x = 91, prove x = 7.
    intro h
    have h1 : x^2 + 6 * x - 91 = 0 := by linarith
    have h2 : (x - 7) * (x + 13) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where (x - 7) = 0, which implies x = 7.
      linarith
    · -- Case where (x + 13) = 0, which contradicts with x > 0.
      linarith
  · -- Backward direction: Assume x = 7, prove x^2 + 6 * x = 91.
    intro h
    rw [h]
    norm_num