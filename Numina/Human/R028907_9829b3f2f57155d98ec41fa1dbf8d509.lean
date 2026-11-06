import Mathlib

/- 4. Positive numbers $a, b$ and $c$ satisfy the condition $a^{2}+b^{2}+c^{2}=1$. Prove the inequality $\frac{a b}{c}+\frac{b c}{a}+\frac{c a}{b} \geqslant \sqrt{3}$. -/
theorem inequalities_224814 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    Real.sqrt 3 ≤ a * b / c + b * c / a + c * a / b := by
  -- We'll prove that our expression is greater than or equal to √3
  have h4 : a * b / c + b * c / a + c * a / b ≥ Real.sqrt 3 := by
    -- First we'll show that the square of our expression is at least 3
    have h1 : (a * b / c + b * c / a + c * a / b) ^ 2 ≥ 3 := by
      -- Expand the square of the sum using algebraic manipulation
      have h2 : (a * b / c + b * c / a + c * a / b) ^ 2 = (a * b / c) ^ 2 + (b * c / a) ^ 2 + (c * a / b) ^ 2 + 2 * ((a * b / c) * (b * c / a) + (b * c / a) * (c * a / b) + (c * a / b) * (a * b / c)) := by
        ring
      rw [h2]
      -- Simplify the cross-terms to show they equal a²+b²+c²
      have h3 : (a * b / c) * (b * c / a) + (b * c / a) * (c * a / b) + (c * a / b) * (a * b / c) = a^2 + b^2 + c^2 := by
        field_simp
        ring
      rw [h3, h]
      -- Prove that the sum of squares of our terms is at least 1
      have h4 : (a * b / c) ^ 2 + (b * c / a) ^ 2 + (c * a / b) ^ 2 ≥ 1 := by
        -- Use the fact that sum of squares of differences is non-negative
        have _ : (a * b / c - b * c / a) ^ 2 + (b * c / a - c * a / b) ^ 2 + (c * a / b - a * b / c) ^ 2 ≥ 0 := by
          nlinarith [sq_nonneg (a * b / c - b * c / a), sq_nonneg (b * c / a - c * a / b), sq_nonneg (c * a / b - a * b / c)]
        nlinarith
      nlinarith [h4]
    -- Prove that our expression is non-negative (needed for taking square root)
    have h5 : a * b / c + b * c / a + c * a / b ≥ 0 := by
      apply add_nonneg
      apply add_nonneg
      -- Show that ab/c ≥ 0
      · apply div_nonneg
        · apply mul_nonneg
          · linarith
          · linarith
        · linarith
      -- Show that bc/a ≥ 0
      · apply div_nonneg
        · apply mul_nonneg
          · linarith
          · linarith
        · linarith
      -- Show that ca/b ≥ 0
      · apply div_nonneg
        · apply mul_nonneg
          · linarith
          · linarith
        · linarith
    -- Use the fact that √3² = 3
    have h7 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    -- Apply the square root property: if x² ≥ y² and x ≥ 0, then x ≥ y
    nlinarith [h1, Real.le_sqrt_of_sq_le (show (Real.sqrt 3) ^ 2 ≤ (a * b / c + b * c / a + c * a / b) ^ 2 by nlinarith)]
  -- Complete the proof using the inequality we've established
  linarith [h4]
