import Mathlib

/- Prove that if $x, y, z$ are reals, then $x^2(3y^2+3z^2-2yz)=>yz(2xy+2xz-yz)$ -/
theorem inequalities_65799 (x y z : ℝ) : x^2 * (3 * y^2 + 3 * z^2 - 2 * y * z) ≥ y * z * (2 * x * y + 2 * x * z - y * z) := by
  ring_nf
  nlinarith [sq_nonneg (x * y - x * z), sq_nonneg (x * z - y * z), sq_nonneg (2 * x * y - 2 * x * z), sq_nonneg (2 * x * z - y * z), sq_nonneg (y * z - 2 * y * z)]