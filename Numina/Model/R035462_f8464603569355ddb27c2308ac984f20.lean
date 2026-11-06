import Mathlib
open Real

theorem inequalities_1573 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : (x + y + z) * (x * y + z * x + y * z) = 1) :
  x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≤ 1 - 6 * x * y * z := by 
  have h1 : 0 ≤ x * y * z := by
    apply mul_nonneg
    apply mul_nonneg
    all_goals linarith
  have h2 : x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≤ (x + y + z) * (x * y + x * z + y * z) - 6 * x * y * z := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
      mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx, mul_nonneg (mul_nonneg hx hy) hz
    ]
  have h3 : (x + y + z) * (x * y + x * z + y * z) = 1 := by
    linarith
  linarith [h2, h3]