import Mathlib
/- Let $a, b, c$ be the three roots of $p(x)=x^{3}+x^{2}-333 x-1001$. Find $a^{3}+b^{3}+c^{3}$. -/
theorem algebra_611090 (a b c : ℂ) (h : ∀ x : ℝ, x ^ 3 + x ^ 2 - 333 * x - 1001 = (x - a) * (x - b) * (x - c)) : a ^ 3 + b ^ 3 + c ^ 3 = 2003:= by
  -- Evaluate the polynomial at x = 0
  have h1:= h 0
  -- Evaluate the polynomial at x = 1
  have h2:= h 1
  -- Evaluate the polynomial at x = -1
  have h3:= h (-1)

  -- Simplify the expressions using ring normalization
  ring_nf at h1 h2 h3
  -- Further simplify the expressions
  simp at h1 h2 h3

  -- Use linear combination of equations to prove the result
  -- This combines the equations with specific coefficients to reach the desired conclusion
  linear_combination
    (a ^ 2 + b ^ 2 + c ^ 2 - 1 * a - 1 * b - 1 * c + 331) * h1 +
        (1 / 2 * a ^ 2 + 1 / 2 * b ^ 2 + 1 / 2 * c ^ 2 + 166) * h2 +
      (1 / 2 * a ^ 2 + 1 / 2 * b ^ 2 + 1 / 2 * c ^ 2 - 1 * a - 1 * b - 1 * c + 168) * h3
