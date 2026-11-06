import Mathlib
/- If $x y=5$ and $x^{2}+y^{2}=21$, compute $x^{4}+y^{4}$. -/
theorem algebra_611151 (x y : ℝ) (h1 : x * y = 5) (h2 : x ^ 2 + y ^ 2 = 21) : x ^ 4 + y ^ 4 = 391:= by
  -- Solution approach:
  -- 1. Use the identity: x⁴+y⁴ = (x²+y²)² - 2(xy)²
  rw [show x ^ 4 + y ^ 4 = (x ^ 2 + y ^ 2) ^ 2 - 2 * (x * y) ^ 2 by ring]
  -- 2. Substitute the given conditions
  rw [h1, h2]
  -- 3. Simplify to get the final result
  ring_nf
