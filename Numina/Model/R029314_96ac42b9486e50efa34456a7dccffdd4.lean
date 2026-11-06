import Mathlib

theorem algebra_213309 {x y z : ℤ} (h₀ : x^2 - 23 * y - 25 * z = -681) (h₁ : y^2 - 21 * x - 21 * z = -419) (h₂ : z^2 - 19 * x - 21 * y = -313) :
    (x, y, z) = (20, 22, 23) := by
  have h3 : (x - 20) ^ 2 + (y - 22) ^ 2 + (z - 23) ^ 2 = 0 := by
    nlinarith
  have hx1 : (x - 20) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - 20), sq_nonneg (y - 22), sq_nonneg (z - 23)]
  have hy1 : (y - 22) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 20), sq_nonneg (y - 22), sq_nonneg (z - 23)]
  have hz1 : (z - 23) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 20), sq_nonneg (y - 22), sq_nonneg (z - 23)]
  have hx2 : x - 20 = 0 := by
    rwa [sq_eq_zero_iff] at hx1
  have hy2 : y - 22 = 0 := by
    rwa [sq_eq_zero_iff] at hy1
  have hz2 : z - 23 = 0 := by
    rwa [sq_eq_zero_iff] at hz1
  have hx3 : x = 20 := by
    linarith
  have hy3 : y = 22 := by
    linarith
  have hz3 : z = 23 := by
    linarith
  simp [Prod.ext_iff, hx3, hy3, hz3]