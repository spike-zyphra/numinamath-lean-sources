import Mathlib

theorem inequalities_598298 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ((x + y + z) * x - y * z) * (y + z) ^ 2 +
    ((x + y + z) * y - z * x) * (z + x) ^ 2 +
    ((x + y + z) * z - x * y) * (x + y) ^ 2 ≤
    (x + y + z) * (x + y) * (y + z) * (z + x) := by 
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
  sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
  sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y), 
  mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx, 
  mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith), 
  mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ x by linarith), 
  mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith)]