import Mathlib

theorem algebra_86320 {x y z p : ℝ} (h₀ : x^2 - 3 * y + p = z) (h₁ : y^2 - 3 * z + p = x)
    (h₂ : z^2 - 3 * x + p = y) (h₃ : p ≥ 4) :
    x = 2 ∧ y = 2 ∧ z = 2 := by
  have h₄ : x^2 + y^2 + z^2 - 4 * x - 4 * y - 4 * z + 3 * p = 0 := by
    nlinarith
  have h₅ : (x - 2)^2 + (y - 2)^2 + (z - 2)^2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
  have hx : (x - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
  have hy : (y - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
  have hz : (z - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]
  have hx2 : x - 2 = 0 := by
    rw [sq_eq_zero_iff] at hx
    linarith
  have hy2 : y - 2 = 0 := by
    rw [sq_eq_zero_iff] at hy
    linarith
  have hz2 : z - 2 = 0 := by
    rw [sq_eq_zero_iff] at hz
    linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith