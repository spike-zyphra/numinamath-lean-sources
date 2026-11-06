import Mathlib
set_option maxHeartbeats 800000
/- 53. Positive numbers $x, y, z$ satisfy $x+y+z+x^{2}+y^{2}+z^{2}=6$, prove that $x^{2} y+y^{2} z+z^{2} x \leqslant 3$ -/
theorem inequalities_601452 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z + x^2 + y^2 + z^2 = 6) :
    x^2 * y + y^2 * z + z^2 * x ≤ 3 := by
  -- The proof uses the nlinarith tactic with several non-negative square expressions
  -- These include squares of: (x+y+z-3), (x-y), (y-z), (z-x), (x-1), (y-1), (z-1)
  -- The nlinarith tactic can automatically solve the inequality using these non-negative expressions
  nlinarith [sq_nonneg (x + y + z - 3), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
