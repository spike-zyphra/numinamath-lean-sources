import Mathlib

theorem algebra_249117 (k : ℝ) (h : ∀ x, 2*x^2-2*k*x+(k^2+2*k+2) > x^2+2*k*x-2*k^2-1) :
    -1 < k ∧ k < 3 := by
  have h1 : ∀ x, x^2 - 4 * k * x + 3 * k^2 + 2 * k + 3 > 0 := by
    intro x
    have h2 := h x
    linarith
  have h3 := h1 (2 * k)
  have h4 : -k ^ 2 + 2 * k + 3 > 0 := by
    nlinarith
  constructor
  · -- Solving quadratic inequality
    nlinarith [sq_nonneg (k - 3), sq_nonneg (k + 1)]
  · -- Solving quadratic inequality
    nlinarith [sq_nonneg (k - 3), sq_nonneg (k + 1)]