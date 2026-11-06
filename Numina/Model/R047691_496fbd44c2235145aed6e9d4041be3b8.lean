import Mathlib

theorem inequalities_306868 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 9 * x * y * z + x * y + y * z + z * x = 4) :
    x * y + y * z + z * x ≥ 4 / 3 ∧ x + y + z ≥ 2 := by 
  have h1 : x * y + y * z + z * x ≥ 4 / 3 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
  have h2 : x + y + z ≥ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          h1, h]
  constructor 
  · exact h1
  · exact h2