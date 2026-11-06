import Mathlib

/- If $(2x + 3y)^2 = 4$ and $xy = -5$, what is the value of $4x^2 + 9y^2$? -/
theorem algebra_19278 {x y : ℝ} (h₀ : (2 * x + 3 * y) ^ 2 = 4) (h₁ : x * y = -5) :
    4 * x ^ 2 + 9 * y ^ 2 = 64 := by
  -- notice that 4x^2+9y^2 = (2x+3y)^2-12xy
  have h1: 4*x^2+9*y^2 = (2*x+3*y)^2-12*(x*y) := by ring
  -- and (2x+3y)^2=4, xy = -5. substitute back, it is 4 - 12(-5) = 64
  rw [h1, h₀, h₁]; norm_num