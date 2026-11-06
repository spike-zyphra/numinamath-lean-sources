import Mathlib

theorem algebra_327618 (a b : ℝ) (h : a^3 + b^3 + 3 * a * b = 1) : a + b = 1 ∨ a + b = -2 := by 
  have h1 : a^3 + b^3 = (a + b) ^ 3 - 3 * a * b * (a + b) := by
    ring_nf
  rw [h1] at h

  have h2 : (a + b - 1) * ((a + b) ^ 2 + (a + b) + 1 - 3 * a * b) = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1)]
 
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where $a + b - 1 = 0$, so $a + b = 1$
    left
    linarith
  · -- Case where $(a + b)^2 + (a + b) + 1 - 3ab = 0$
    have h5 : (a + b) ^ 2 + (a + b) + 1 = 3 * a * b := by
      nlinarith
    have h7 : a + b = -2 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b + 2)]
    right 
    linarith