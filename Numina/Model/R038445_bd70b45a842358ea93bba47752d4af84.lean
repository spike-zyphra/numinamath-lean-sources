import Mathlib

open Real

theorem inequalities_87230 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    sqrt (7 * x + 3) + sqrt (7 * y + 3) + sqrt (7 * z + 3) ≤ 7 := by
  have h1 : 0 < 7 * x + 3 := by nlinarith
  have h2 : 0 < 7 * y + 3 := by nlinarith
  have h3 : 0 < 7 * z + 3 := by nlinarith
  have h4 : sqrt (7 * x + 3) + sqrt (7 * y + 3) + sqrt (7 * z + 3) ≤ 7 := by
    nlinarith [sq_nonneg (sqrt (7 * x + 3) - 2), sq_nonneg (sqrt (7 * y + 3) - 2), sq_nonneg (sqrt (7 * z + 3) - 2),
      Real.sqrt_nonneg (7 * x + 3), Real.sqrt_nonneg (7 * y + 3), Real.sqrt_nonneg (7 * z + 3),
      Real.sq_sqrt (show 0 ≤ 7 * x + 3 by linarith), Real.sq_sqrt (show 0 ≤ 7 * y + 3 by linarith), Real.sq_sqrt (show 0 ≤ 7 * z + 3 by linarith),
      mul_nonneg (Real.sqrt_nonneg (7 * x + 3)) (Real.sqrt_nonneg (7 * y + 3)), 
      mul_nonneg (Real.sqrt_nonneg (7 * x + 3)) (Real.sqrt_nonneg (7 * z + 3)), 
      mul_nonneg (Real.sqrt_nonneg (7 * y + 3)) (Real.sqrt_nonneg (7 * z + 3)), 
      hsum, 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
  exact h4