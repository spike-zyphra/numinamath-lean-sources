import Mathlib

theorem algebra_322319 {x y z : ℝ} (hxyz : x * y * z = 1) (hsum : x + y + z = 2)
    (hsumsq : x^2 + y^2 + z^2 = 16) :
    1 / (x * y + 2 * z) + 1 / (y * z + 2 * x) + 1 / (z * x + 2 * y) = -4 / 13 := by

  have hxy : x * y + y * z + z * x = -6 := by
    have h : x^2 + y^2 + z^2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by
      nlinarith
    rw [hsum] at h
    nlinarith

  have h1 : x * y + 2 * z ≠ 0 := by
    by_contra h'
    have h2 : x * y * z = 0 := by
      nlinarith [sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), h']
    nlinarith

  have h2 : y * z + 2 * x ≠ 0 := by
    by_contra h'
    have h2 : x * y * z = 0 := by
      nlinarith [sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), h']
    nlinarith

  have h3 : z * x + 2 * y ≠ 0 := by
    by_contra h'
    have h2 : x * y * z = 0 := by
      nlinarith [sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), h']
    nlinarith

  field_simp [h1, h2, h3]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z - 2), sq_nonneg (x * y + y * z + z * x + 6), sq_nonneg (x * y * z - 1)]