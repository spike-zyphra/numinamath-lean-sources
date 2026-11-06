import Mathlib

theorem inequalities_321638 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≥ y) (hyz : y ≥ z) (hzx : z > x * y) (hsum : x + y + z = 1) :
    x * y * z + 2 * Real.sqrt (x * y * z) > x * y + y * z + z * x := by 
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h2 : 0 < x * y := by nlinarith
  have h3 : Real.sqrt (x * y * z) ≥ 0 := by positivity
  have h4 : Real.sqrt (x * y * z) ^ 2 = x * y * z := by
    rw [Real.sq_sqrt]
    positivity
  have hp1 : 0 < Real.sqrt (x * y * z) := by positivity
  have h6 : Real.sqrt (x * y * z) > (x * y + y * z + z * x - x * y * z) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (x * y * z) - (x * y + y * z + z * x - x * y * z) / 2), 
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_nonneg (show 0 ≤ y - z by nlinarith) (show 0 ≤ x - y by nlinarith),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, Real.sq_sqrt (show x * y * z ≥ 0 by positivity),
      mul_pos (show 0 < z by nlinarith) (show 0 < y * z by nlinarith)
    ]
  nlinarith [Real.sq_sqrt (show x * y * z ≥ 0 by positivity), Real.sqrt_nonneg (x * y * z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h4, h6]