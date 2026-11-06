import Mathlib

theorem algebra_325889 {x y z : ℝ} (hxy : x ≠ y) (h1 : x^2 * (y + z) = 2019) (h2 : y^2 * (z + x) = 2019) :
    z^2 * (x + y) - x * y * z = 4038 := by

  have h3 : x^2 * (y + z) = y^2 * (z + x) := by 
    linarith
  have h4 : x^2 * (y + z) - y^2 * (z + x) = 0 := by
    linarith
  have h5 : (x - y) * (x * y + z * (x + y)) = 0 := by
    ring_nf at h4 ⊢
    linarith

  have h6 : x * y + z * (x + y) = 0 := by 
    apply (mul_left_inj' (sub_ne_zero.mpr hxy)).mp 
    linarith
  
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hxy), sq_nonneg (x - y), sq_nonneg (x + y - z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), h6]