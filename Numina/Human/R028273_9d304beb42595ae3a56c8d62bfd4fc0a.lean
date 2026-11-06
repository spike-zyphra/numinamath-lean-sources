import Mathlib

/- Let $x$ and $y$ be positive real numbers such that $x + y = 1$. Show that $$\left( \frac{x+1}{x} \right)^2  + \left( \frac{y+1}{y} \right)^2 \geq 18.$$ -/
theorem inequalities_89372 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    ((x + 1) / x) ^ 2 + ((y + 1) / y) ^ 2 ≥ 18 := by
  -- Rewrite the expression in a more convenient form
  have h1 : ((x + 1) / x) ^ 2 + ((y + 1) / y) ^ 2 = (1 + 1 / x) ^ 2 + (1 + 1 / y) ^ 2 := by
    field_simp
  rw [h1]

  -- Expand the squared terms
  have h2 : (1 + 1 / x) ^ 2 + (1 + 1 / y) ^ 2 = 2 + 2 * (1 / x + 1 / y) + (1 / x ^ 2 + 1 / y ^ 2) := by
    field_simp
    ring
  rw [h2]

  -- Prove that 1/x + 1/y ≥ 4
  have h3 : 1 / x + 1 / y ≥ 4 := by
    -- Algebraic manipulation to prepare for the inequality proof
    have h4 : 1 / x + 1 / y - 4 = (x + y - 4 * x * y) / (x * y) := by
      field_simp
      nlinarith
    -- Show that the numerator is non-negative
    have h5 : x + y - 4 * x * y ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1)]
    -- Show that the entire fraction is non-negative
    have h6 : (x + y - 4 * x * y) / (x * y) ≥ 0 := by
      apply div_nonneg
      · linarith
      · nlinarith [mul_pos hx hy]
    linarith

  -- Prove that 1/x² + 1/y² ≥ 8
  have h4 : 1 / x ^ 2 + 1 / y ^ 2 ≥ 8 := by
    -- Use the AM-GM inequality and the fact that 1/x + 1/y ≥ 4
    have h6 : (1 / x + 1 / y) ^ 2 - 2 * (1 / x) * (1 / y) - 8 ≥ 0 := by
      nlinarith [sq_nonneg (1 / x - 1 / y), h3]
    linarith

  -- Combine the inequalities to prove the original statement
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), h3, h4]
