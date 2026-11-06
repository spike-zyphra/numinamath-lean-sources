import Mathlib

theorem inequalities_162856 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    2 * Real.sqrt 3 ≤ 1 / x + 1 / y + 1 / z - (x + y + z) := by 
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ 3 by norm_num)
  have h3 : 2 * Real.sqrt 3 ≥ 0 := by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  -- Next, we manipulate the inequality
  -- Multiply the inequality by numerator cyclic reciprocals:
  -- x*y*z to clear denominators.
  have h4 : 1 / x + 1 / y + 1 / z - (x + y + z) = (y * z + x * z + x * y - (x + y + z) * (x * y * z)) / (x * y * z) := by
    field_simp
    ring
  rw [h4] at *
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
    sq_nonneg (x + y + z - Real.sqrt 3), sq_nonneg (x * y * z - (Real.sqrt 3) / 27),
    h, h1, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]