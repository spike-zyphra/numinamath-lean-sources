import Mathlib

/- Example 4 Let $x \geqslant 0, y \geqslant 0, x^{2}+\frac{y^{2}}{2}=1$, then the maximum value of $x \sqrt{1+y^{2}}$ is $\qquad$ -/
theorem algebra_597771 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^2 + y^2 / 2 = 1) :
    x * Real.sqrt (1 + y^2) ≤ 3 * Real.sqrt 2 / 4 := by
  -- Restating the constraint equation for clarity
  have h1 : x^2 + y^2 / 2 = 1 := h

  -- Main proof: showing that x√(1+y^2) ≤ 3√2/4
  have h2 : x * Real.sqrt (1 + y^2) ≤ 3 * Real.sqrt 2 / 4 := by
    -- We'll prove this by squaring both sides
    have h3 : (x * Real.sqrt (1 + y^2)) ^ 2 ≤ (3 * Real.sqrt 2 / 4) ^ 2 := by
      -- Simplifying the left side of the inequality
      have h4 : (x * Real.sqrt (1 + y^2)) ^ 2 = x^2 * (1 + y^2) := by
        calc
          (x * Real.sqrt (1 + y^2)) ^ 2
              = x^2 * (Real.sqrt (1 + y^2) ^ 2) := by ring
          _ = x^2 * (1 + y^2) := by
            -- Using the property that (√a)² = a for a ≥ 0
            have h5 : Real.sqrt (1 + y^2) ^ 2 = 1 + y^2 := by
              apply Real.sq_sqrt
              nlinarith [sq_nonneg y]
            rw [h5]
      -- Simplifying the right side of the inequality
      have h6 : (3 * Real.sqrt 2 / 4 : ℝ) ^ 2 = 9 / 8 := by
        calc
          (3 * Real.sqrt 2 / 4 : ℝ) ^ 2
              = (9 * (Real.sqrt 2) ^ 2) / 16 := by ring
          _ = (9 * 2) / 16 := by
            -- Using the property that (√2)² = 2
            have h7 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
            rw [h7]
          _ = 9 / 8 := by norm_num
      -- Substituting the simplified expressions and using nonlinear arithmetic
      rw [h4]
      nlinarith [sq_nonneg (x - Real.sqrt 3 / 2), sq_nonneg (y - Real.sqrt 2 / 2),
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
        h1, mul_self_nonneg (y ^ 2 - 1 / 2), mul_self_nonneg (x - Real.sqrt 3 / 2),
        mul_self_nonneg (y - Real.sqrt 2 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + y^2) by nlinarith [sq_nonneg y])]
    -- Concluding the proof using the squared inequality and nonnegativity of terms
    nlinarith [h3, Real.sqrt_nonneg (1 + y^2), Real.sqrt_nonneg 2, mul_nonneg hx (Real.sqrt_nonneg (1 + y^2))]
  -- Final step: using the proven inequality
  linarith
