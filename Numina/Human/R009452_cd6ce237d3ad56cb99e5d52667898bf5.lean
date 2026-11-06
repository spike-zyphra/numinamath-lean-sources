import Mathlib

/- Let $a=\frac{3}{5}$ and let $b=\frac{2}{3}$. Compute $a^{2}b^{-3}.$ -/
theorem algebra_16667 {a b : ℝ} (ha : a = 3 / 5) (hb : b = 2 / 3) : a^2 * b^(-3 : ℤ) = 243 / 200 := by
  rw [ha, hb]
  norm_num