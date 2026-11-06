import Mathlib
set_option maxHeartbeats 800000
/- 18. Let $x, y, z$ be three positive real numbers, and $x y z=1$, prove that: $x^{2}+y^{2}+z^{2}+x+y+z \geqslant$ $2(x y+y z+z x)$. (2000 Moscow Mathematical Olympiad problem) -/
theorem inequalities_601502 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    x ^ 2 + y ^ 2 + z ^ 2 + x + y + z ≥ 2 * (x * y + y * z + z * x) := by
  -- We use nlinarith tactic with several non-negative expressions
  -- These include squares of differences between products and 1, and squares of differences between variables
  -- We also include positivity of products and the constraint x*y*z = 1
  nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
    hxyz]
