import Mathlib

theorem inequalities_171028 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    2 * (x^3 + y^3 + z^3) ≥ x^2 * y + x^2 * z + y^2 * z + y^2 * x + z^2 * x + z^2 * y := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
            mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]