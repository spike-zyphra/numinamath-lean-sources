import Mathlib

/- Two reals $x$ and $y$ are such that $x-y=4$ and $x^{3}-y^{3}=28$. Compute $x y$.. -/
theorem algebra_608133 (x y : ℝ) (h₁ : x - y = 4) (h₂ : x^3 - y^3 = 28) : x * y = -3 := by
  -- Use the identity x^3 - y^3 = (x - y)(x^2 + xy + y^2).
  replace h₂ : (x - y) * ((x - y)^2 + 3 * x * y) = 28 := by linear_combination h₂
  -- Substitute x - y = 4.
  rw [h₁] at h₂
  -- Solve for xy.
  linarith only [h₂]
