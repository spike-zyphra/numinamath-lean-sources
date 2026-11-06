import Mathlib

theorem algebra_254966 (f : ℝ → ℝ) :
    (∀ x, f x + x * f (1 - x) = x ^ 2 - 1) ↔
    ∀ x, f x = (-x ^ 3 + 3 * x ^ 2 - 1) / (x ^ 2 - x + 1) := by

  constructor
  · -- Assume that ∀ x, f x + x * f (1 - x) = x ^ 2 - 1, prove ∀ x, f x = (-x ^ 3 + 3 * x ^ 2 - 1) / (x ^ 2 - x + 1)
    intro h
    intro x
    have eq1 := h x
    have eq2 := h (1 - x)
    have eq3 : f x + x * f (1 - x) = x ^ 2 - 1 := by
      simpa using eq1
    have eq4 : f (1 - x) + (1 - x) * f x = (1 - x) ^ 2 - 1 := by
      have eq5 : 1 - (1 - x) = x := by
        ring
      rw [eq5] at eq2
      linarith [eq2]

    have eq5 : f x = (-x ^ 3 + 3 * x ^ 2 - 1) / (x ^ 2 - x + 1) := by
      have h6 : x ^ 2 - x + 1 ≠ 0 := by
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 2)]
      have h11 : f x * (x^2 - x + 1) = -x ^ 3 + 3 * x ^ 2 - 1 := by
        nlinarith [eq3, eq4]
      have h12 : f x = (-x ^ 3 + 3 * x ^ 2 - 1) / (x ^ 2 - x + 1) := by
        field_simp [h6]
        linarith [h11]
      exact h12
    exact eq5
  · -- Assume that ∀ x, f x = (-x ^ 3 + 3 * x ^ 2 - 1) / (x ^ 2 - x + 1), prove ∀ x, f x + x * f (1 - x) = x ^ 2 - 1
    intro h x
    have h1 : f x = (-x ^ 3 + 3 * x ^ 2 - 1) / (x ^ 2 - x + 1) := h x
    have h2 : f (1 - x) = (-(1 - x) ^ 3 + 3 * (1 - x) ^ 2 - 1) / ((1 - x) ^ 2 - (1 - x) + 1) := h (1 - x)
    rw [h1, h2]
    have h3 : (x ^ 2 - x + 1 : ℝ) ≠ 0 := by
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 2)]
    have h4 : ((1 - x) ^ 2 - (1 - x) + 1 : ℝ) ≠ 0 := by
      nlinarith [sq_nonneg ((1 - x) - 1 / 2), sq_nonneg ((1 - x) - 2)]
    field_simp [h3, h4]
    ring