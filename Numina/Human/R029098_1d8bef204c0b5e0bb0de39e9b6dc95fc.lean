import Mathlib

/- 4A. Determine all real functions $f$ defined for every real number $x$, such that $f(x) + x f(1-x) = x^2 - 1$. -/
theorem algebra_254966 (f : ℝ → ℝ) :
    (∀ x, f x + x * f (1 - x) = x ^ 2 - 1) ↔
    ∀ x, f x = (-x ^ 3 + 3 * x ^ 2 - 1) / (x ^ 2 - x + 1) := by
  constructor
  · -- Assume that f satisfies the functional equation for all x, prove the explicit formula
    intro h
    intro x
    -- Apply the functional equation at point x
    have h1 := h x
    -- Apply the functional equation at point (1-x)
    have h2 := h (1 - x)
    -- Restate the functional equation at x
    have eq1 : f x + x * f (1 - x) = x^2 - 1 := by simpa using h1
    -- Restate the functional equation at (1-x)
    have eq2 : f (1 - x) + (1 - x) * f x = (1 - x) ^ 2 - 1 := by
      simpa using h2
    -- Derive the explicit formula for f(x)
    have eq3 : f x = (-x^3 + 3 * x^2 - 1) / (x^2 - x + 1) := by
      -- Restate the equation (redundant but kept for clarity)
      have eq2' : f (1 - x) + (1 - x) * f x = (1 - x) ^ 2 - 1 := by
        linarith
      -- Multiply the equation by x
      have eq3' : x * f (1 - x) + x * (1 - x) * f x = x * ((1 - x) ^ 2 - 1) := by
        nlinarith [eq2']
      -- Isolate x * f(1-x) from the original equation
      have eq4 : x * f (1 - x) = x^2 - 1 - f x := by
        linarith [eq1]
      -- Substitute and solve for f(x)
      rw [eq4] at eq3'
      -- Prove that the denominator is never zero
      have hne : x^2 - x + 1 ≠ 0 := by
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1)]
      -- Simplify the fraction and solve for f(x)
      field_simp [hne]
      linarith
    exact eq3
  · -- Assume the explicit formula for f(x), prove it satisfies the functional equation
    intro h x
    -- Verify that the explicit formula satisfies the functional equation
    have eq1 : f x + x * f (1 - x) = x^2 - 1 := by
      -- Get the formula values at x and (1-x)
      have hfx := h x
      have hfx1 := h (1 - x)
      simp [hfx, hfx1]
      -- Prove that denominators are never zero
      have hne : (x ^ 2 - x + 1) ≠ 0 := by
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1)]
      have hne1 : ((1 - x) ^ 2 - (1 - x) + 1) ≠ 0 := by
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1)]
      -- Simplify the fractions and verify the equation through algebraic manipulation
      field_simp [hne, hne1]
      ring
    exact eq1
