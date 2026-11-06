import Mathlib

/- Let $x$, $y$, and $z$ be real numbers such that
$$12x - 9y^2 = 7$$
$$6y - 9z^2 = -2$$
$$12z - 9x^2 = 4$$
Find $6x^2 + 9y^2 + 12z^2$. -/
theorem algebra_53868 {x y z : ℝ} (h₁ : 12 * x - 9 * y ^ 2 = 7) (h₂ : 6 * y - 9 * z ^ 2 = -2)
    (h₃ : 12 * z - 9 * x ^ 2 = 4) : 6 * x ^ 2 + 9 * y ^ 2 + 12 * z ^ 2 = 9 := by
  -- Use symmetry in nonlinear equations to reduce complexity
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1 / 3), sq_nonneg (z - 2 / 3)]
  -- The previous lines give conditions based on symmetry and the balance equations implied by squares