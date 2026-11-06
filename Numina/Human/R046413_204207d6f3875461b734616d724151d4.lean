import Mathlib

/- Let $x, y$ and $z$ be positive real numbers. Show that $x^{2}+x y^{2}+x y z^{2} \geq 4 x y z-4$. -/
theorem algebra_605568 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
  x ^ 2 + x * y ^ 2 + x * y * z ^ 2 ≥ 4 * x * y * z - 4 := by
  -- We have x ^ 2 ≥ 4 * x - 4, y ^ 2 ≥ 4 * y - 4, and z ^ 2 ≥ 4 * z - 4.
  -- And therefore x ^ 2 + x * y ^ 2 + x * y * z ^ 2 ≥ (4 * x - 4) + x * (4 * y - 4) + x * y * (4 * z - 4) = 4 * x * y * z - 4.
  have h₁ : x ^ 2 ≥ 4 * x - 4 := by linarith only [sq_nonneg (x - 2)]
  have h₂ : y ^ 2 ≥ 4 * y - 4 := by linarith only [sq_nonneg (y - 2)]
  replace h₂ : x * y ^ 2 ≥ x * (4 * y - 4) := mul_le_mul_of_nonneg_left h₂ (by positivity)
  have h₃ : z ^ 2 ≥ 4 * z - 4 := by linarith only [sq_nonneg (z - 2)]
  replace h₃ : x * y * z ^ 2 ≥ x * y * (4 * z - 4) := mul_le_mul_of_nonneg_left h₃ (by positivity)
  linarith only [h₁, h₂, h₃]
