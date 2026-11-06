import Mathlib

theorem algebra_599494 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxp : x < Real.pi) (hyq : y < Real.pi) (hzr : z < Real.pi) :
    Real.sin (2 * x) + Real.sin (2 * y) + Real.sin (2 * z) < Real.pi := by
  have h1 : Real.sin (2 * x) ≤ 1 := by 
    apply Real.sin_le_one
  have h2 : Real.sin (2 * y) ≤ 1 := by 
    apply Real.sin_le_one
  have h3 : Real.sin (2 * z) ≤ 1 := by 
    apply Real.sin_le_one
  have h4 : Real.sin (2 * x) + Real.sin (2 * y) + Real.sin (2 * z) ≤ 3 := by 
    linarith [h1, h2, h3]
  have h5 : (3 : ℝ) < Real.pi := by
    linarith [Real.pi_gt_three]
  linarith [h4, h5]