import Mathlib

theorem inequalities_190015 (x y z : ℝ) : 4 * x * (x + y) * (x + z) * (x + y + z) + y^2 * z^2 ≥ 0 := by 
  have h1 : 4 * x * (x + y) * (x + z) * (x + y + z) + y^2 * z^2 = (2 * x * (x + y + z) + y * z) ^ 2 := by 
    ring
  rw [h1]
  apply sq_nonneg