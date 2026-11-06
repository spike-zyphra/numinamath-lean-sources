import Mathlib

/- Show that for all positive real numbers $x, y$ and $z$, we have: $x^{2}+y^{4}+z^{6} \geq x y^{2}+y^{2} z^{3}+x z^{3}$. -/
theorem inequalities_104726 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x^2 + y^4 + z^6 ≥ x * y^2 + y^2 * z^3 + x * z^3 := by
    --We use `nlinarith` and `sq_nonneg` as follows.
  nlinarith [sq_nonneg (x - y^2), sq_nonneg (y^2 - z^3), sq_nonneg (z^3 - x),
    sq_nonneg (x - z^3), sq_nonneg (y^2 - x), sq_nonneg (z^3 - y^2),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]