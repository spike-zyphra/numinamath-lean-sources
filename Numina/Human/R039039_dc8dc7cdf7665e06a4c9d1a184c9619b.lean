import Mathlib

/- 11. Let $x, y, z$ be positive numbers, satisfying $x y + y z + z x = 1$. Prove: $x y z (x + y)(y + z)(z + x) \geqslant \left(1 - x^{2}\right)\left(1 - y^{2}\right)\left(1 - z^{2}\right)$. -/
theorem inequalities_246521 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    x * y * z * (x + y) * (y + z) * (z + x) ≥ (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2) := by
  -- Proof using nlinarith tactic with several non-negativity facts:
  -- 1. Squares of differences between products are non-negative: (xy-zx)², (yz-xy)², (zx-yz)²
  -- 2. Squares of differences between variables are non-negative: (x-y)², (y-z)², (z-x)²
  -- 3. Square of the constraint expression minus 1 is non-negative: (xy+yz+zx-1)²
  -- 4. Products of positive numbers are positive: xy > 0, yz > 0, zx > 0
  nlinarith [sq_nonneg (x * y - z * x), sq_nonneg (y * z - x * y), sq_nonneg (z * x - y * z),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x * y + y * z + z * x - 1), mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
