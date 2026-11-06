import Mathlib

/- Simplify $\sqrt{192}$. -/
theorem algebra_21056 : √192 = 8 * √3 := by
  -- notice that 192 = 64*3
  have: (192:ℝ) = 8^2 * 3 := by ring
  rw [this]
  rw [Real.sqrt_mul (sq_nonneg (8:ℝ))]
  simp