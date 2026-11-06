import Mathlib

theorem algebra_55618 {x y z : ℝ} (h₀ : x^2 + 6 * y = -17) (h₁ : y^2 + 4 * z = 1) (h₂ : z^2 + 2 * x = 2) :
    x^2 + y^2 + z^2 = 14 := by
  have h3 : x^2 + y^2 + z^2 + 6 * y + 4 * z + 2 * x = -14 := by
    nlinarith
  
  have h4 : (x + 1) ^ 2 + (y + 3) ^ 2 + (z + 2) ^ 2 = 0 := by
    nlinarith [h3]

  have hx : (x + 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 3), sq_nonneg (z + 2)]

  have hy : (y + 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 3), sq_nonneg (z + 2)]

  have hz : (z + 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 3), sq_nonneg (z + 2)]

  have hx1 : x + 1 = 0 := by
    rwa [sq_eq_zero_iff] at hx

  have hy1 : y + 3 = 0 := by
    rwa [sq_eq_zero_iff] at hy

  have hz1 : z + 2 = 0 := by
    rwa [sq_eq_zero_iff] at hz
  
  have hx2 : x = -1 := by
    linarith

  have hy2 : y = -3 := by
    linarith

  have hz2 : z = -2 := by
    linarith

  rw [hx2, hy2, hz2]
  norm_num