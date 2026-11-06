import Mathlib

theorem algebra_101234 (x y z : ℝ) (hx : 20 ≤ x) (hy : 40 ≤ y) (hz : 1675 ≤ z)
    (hsum : x + y + z = 2015) :
    x * y * z ≤ 48407500 := by 
  have h1 : z = 2015 - x - y := by
    linarith
  rw [h1]
  nlinarith [sq_nonneg (x - 170), sq_nonneg (y - 170), sq_nonneg ((2015 - x - y) - 1675),
      mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy),
      mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr (by linarith : (1675 : ℝ) ≤ 2015 - x - y)),
      mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr (by linarith : (1675 : ℝ) ≤ 2015 - x - y))]