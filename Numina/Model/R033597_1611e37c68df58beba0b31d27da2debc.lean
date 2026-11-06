import Mathlib

theorem algebra_213256 {x y z : ℤ} (h1 : x^2 + 25*y + 19*z = -471) (h2 : y^2 + 23*x + 21*z = -397)
    (h3 : z^2 + 21*x + 21*y = -545) :
    (x, y, z) = (-22, -23, -20) := by
  have h4 : (x + 22) ^ 2 + (y + 23) ^ 2 + (z + 20) ^ 2 = 0 := by
    nlinarith
  have h5 : (x + 22) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + 22), sq_nonneg (y + 23), sq_nonneg (z + 20)]
  have h6 : (y + 23) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + 22), sq_nonneg (y + 23), sq_nonneg (z + 20)]
  have h7 : (z + 20) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + 22), sq_nonneg (y + 23), sq_nonneg (z + 20)]
  have h8 : x + 22 = 0 := by
    rwa [sq_eq_zero_iff] at h5
  have h9 : y + 23 = 0 := by
    rwa [sq_eq_zero_iff] at h6
  have h10 : z + 20 = 0 := by
    rwa [sq_eq_zero_iff] at h7
  have hx : x = -22 := by
    linarith
  have hy : y = -23 := by
    linarith
  have hz : z = -20 := by
    linarith
  simp [Prod.ext_iff, hx, hy, hz]