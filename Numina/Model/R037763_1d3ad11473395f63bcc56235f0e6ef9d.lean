import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem inequalities_146837 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hsum : x + y + z = 3) :
  Real.sqrt x + Real.sqrt y + Real.sqrt z ≥ x * y + y * z + z * x := by
  nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt y - 1), sq_nonneg (Real.sqrt z - 1),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z,
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ z by linarith)]