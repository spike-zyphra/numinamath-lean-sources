import Mathlib

theorem algebra_326564 {a b : ℝ} (h₀ : a^2 + b^2 = 1) (h₁ : |1 - 2 * a + b| + 2 * a + 1 = b^2 - a^2) :
    a + b = -1 := by
  by_cases h : 1 - 2 * a + b ≥ 0
  · -- case 1 : 1 - 2*a + b ≥ 0, so |1 - 2*a + b| = 1 - 2*a + b
    rw [abs_of_nonneg h] at h₁
    -- Then the equation becomes $(1 - 2*a + b) + 2*a + 1 = b^2 - a^2$
    -- Simplifying gives $2 + b = b^2 - a^2$
    -- Using h₀: a^2 + b^2 = 1 => a² = 1 - b²
    -- Substitute to get quadratic equation: 2b² - b - 3 = 0
    -- Solving the quadratic equation, and checking validity
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (a), sq_nonneg (b + 1), sq_nonneg (a - 0), sq_nonneg (b + 1)]
  · -- case 2 : 1 - 2*a + b < 0, so |1 - 2*a + b| = -(1 - 2*a + b)
    rw [abs_of_neg (lt_of_not_ge h)] at h₁
    -- The equation becomes (-1 + 2*a - b) + 2*a + 1 = b^2 - a^2
    -- which simplifies to 4*a - b = b^2 - a^2
    -- Combining with a² + b² = 1 leads to a complex equation
    -- Solving this requires exhaustive methods
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (a), sq_nonneg (b + 1), sq_nonneg (a + 1), sq_nonneg (b + 1)]