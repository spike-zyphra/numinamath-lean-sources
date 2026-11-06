import Mathlib
/- Find $x-y$, given that $x^{4}=y^{4}+24, x^{2}+y^{2}=6$, and $x+y=3$. -/
theorem algebra_610839 (x y : ℝ) (h1 : x ^ 4 = y ^ 4 + 24) (h2 : x ^ 2 + y ^ 2 = 6) (h3 : x + y = 3) : x - y = 4 / 3:= by
  -- Replace h1 with a more useful form
  replace h1 : (x ^ 2 + y ^ 2) * (x + y) * (x - y) = 24:= by linarith
  -- Substitute h2 and h3 into h1
  rw [h2, h3] at h1
  -- Simplify the equation
  linarith
