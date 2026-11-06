import Mathlib

theorem inequalities_189407 (α : Real) : 4 * Real.sin (3 * α) + 5 ≥ 4 * Real.cos (2 * α) + 5 * Real.sin α := by
  have h1 : Real.sin (3 * α) = 3 * Real.sin α - 4 * Real.sin α ^ 3 := by
    rw [Real.sin_three_mul]
  have h2 : Real.cos (2 * α) = 1 - 2 * Real.sin α ^ 2 := by
    rw [Real.cos_two_mul, Real.sin_sq]
    <;> ring
  rw [h1, h2]
  nlinarith [sq_nonneg (Real.sin α - 1), sq_nonneg (Real.sin α + 1 / 4),
    Real.sin_sq_add_cos_sq α, sq_nonneg (Real.sin α ^ 2 - 1 / 16),
    sq_nonneg (Real.sin α - 1), sq_nonneg (Real.sin α + 1 / 4)]