import Mathlib

theorem algebra_9204 (x : ℝ) (hx : x ^ 3 - 4 * x = 0) : x = 0 ∨ x = -2 ∨ x = 2 := by
  have h1 : x * (x ^ 2 - 4) = 0 := by
    ring_nf
    linarith
  cases' (mul_eq_zero.mp h1) with hx1 hx2
  · left
    exact hx1
  · -- Solve x^2 - 4 = 0
    have h2 : x^2 - 4 = 0 := hx2
    have h3 : (x - 2) * (x + 2) = 0 := by
      nlinarith [h2]
    cases' (mul_eq_zero.mp h3) with hx3 hx4
    · -- Case x - 2 = 0, so x = 2
      right
      right
      linarith
    · -- Case x + 2 = 0, so x = -2
      right
      left
      linarith