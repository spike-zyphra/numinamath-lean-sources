import Mathlib

/- Let $x,y$ and $z$ be non-negative real numbers satisfying the equation $x+y+z=xyz$. Prove that $2(x^2+y^2+z^2)\geq3(x+y+z)$. -/
theorem inequalities_87968 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x + y + z = x * y * z) :
    2 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 3 * (x + y + z) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]