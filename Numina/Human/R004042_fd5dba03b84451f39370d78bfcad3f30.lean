import Mathlib

/- 2. Let $x, y, z$ be positive real numbers such that $x y + y z + z x = 27$. Prove the inequality


$$

x + y + z \geq \sqrt{3 x y z}

$$
 -/
theorem inequalities_232783 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 27) :
    x + y + z ≥ Real.sqrt (3 * x * y * z) := by
  --show (x + y + z) ^ 2 ≥ 3 * x * y * z.
  have h1 : (x + y + z) ^ 2 ≥ 3 * x * y * z := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (y - z)), sq_nonneg (y * (x - z)), sq_nonneg (z * (x - y)),
          h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  --show (Real.sqrt (3 * x * y * z)) ^ 2 = 3 * x * y * z.
  have h2 : (Real.sqrt (3 * x * y * z)) ^ 2 = 3 * x * y * z := by
    rw [Real.sq_sqrt]
    positivity
  --show 0 ≤ Real.sqrt (3 * x * y * z).
  have h3 : 0 ≤ Real.sqrt (3 * x * y * z) := by positivity
  --show 0 < x + y + z.
  have h4 : 0 < x + y + z := by nlinarith [hx, hy, hz]
  nlinarith [h1, h2, h3, h4, Real.sqrt_nonneg (3 * x * y * z)]