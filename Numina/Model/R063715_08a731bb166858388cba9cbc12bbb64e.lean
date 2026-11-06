import Mathlib

theorem algebra_186643 (x : ℝ) : (x-1)*(x^2-3) + (2*x-1)*(x^2+2) = 3 ↔ x = 1 := by
  constructor
  · -- Assume (x-1)*(x^2-3) + (2*x-1)*(x^2+2) = 3, prove x = 1
    intro h
    have h_eq : (x - 1) * (x ^ 2 - 3) + (2 * x - 1) * (x ^ 2 + 2) = 3 := by
      linarith
    have eq : (x - 1) * (x ^ 2 - 3) + (2 * x - 1) * (x ^ 2 + 2) = 3 * x ^ 3 - 2 * x ^ 2 + x + 1 := by
      ring
    rw [eq] at h_eq
    have h_sub : 3 * x ^ 3 - 2 * x ^ 2 + x + 1 - 3 = 0 := by
      linarith
    have h_cub : 3 * x ^ 3 - 2 * x ^ 2 + x - 2 = 0 := by
      linarith
    have factored : (x - 1) * (3 * x ^ 2 + x + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp factored) with h1 h2
    · -- Case where x - 1 = 0, so x = 1
      linarith
    · -- Case where 3x^2 + x + 2 = 0 
      have h3 : 3 * x ^ 2 + x + 2 = 0 := by linarith
      have h4 : 3 * x ^ 2 + x + 2 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 6)]
      nlinarith
  · -- Assume x = 1, prove (x-1)*(x^2-3) + (2*x-1)*(x^2+2) = 3
    intro h_eq
    rw [h_eq]
    norm_num