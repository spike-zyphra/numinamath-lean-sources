import Mathlib
/- Let $P(x)=x^{3}+x^{2}-r^{2} x-2020$ be a polynomial with roots $r, s, t$. What is $P(1)$ ? -/
theorem algebra_610112 (r s t : ℂ) (h : ∀ x : ℂ, x ^ 3 + x ^ 2 - r ^ 2 * x - 2020 = (x - r) * (x - s) * (x - t)) : 1 ^ 3 + 1 ^ 2 - r ^ 2 * 1 - 2020 = -4038:= by
  -- Apply the polynomial equation with x = r
  have h1:= h r
  -- Simplify the equation
  simp at h1
  -- Normalize the ring expression
  ring_nf at h1
  -- Use linear combination to solve the equation
  linear_combination -(1 * h1)
