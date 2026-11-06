import Mathlib.Tactic

theorem inequalities_137970 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x^2 + 2)*(y^2 + 2)*(z^2 + 2) ≥ 9*(x*y + y*z + z*x) := by
  nlinarith [sq_nonneg (x*y - 1), sq_nonneg (y*z - 1), sq_nonneg (z*x - 1),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x*y*z - 1), sq_nonneg (x + y + z - 2), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
          ]