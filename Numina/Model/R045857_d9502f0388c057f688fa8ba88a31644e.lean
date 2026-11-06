import Mathlib

theorem inequalities_48847 (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    (x^2 - 2 * x + 2) * (y^2 - 2 * y + 2) * (z^2 - 2 * z + 2) ≤ (x * y * z)^2 - 2 * x * y * z + 2 := by
  nlinarith [sq_nonneg (x * y * z - 1), sq_nonneg (x * y - 1), sq_nonneg (x * z - 1), 
  sq_nonneg (y * z - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
  mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy), 
  mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hz), 
  mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hz), 
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)) (sub_nonneg.mpr hz)]