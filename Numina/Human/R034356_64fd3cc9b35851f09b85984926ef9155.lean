import Mathlib

/- Theorem: Given positive real numbers a, b, c such that a * b * c = 1,
the sum a / (a^2 + 2) + b / (b^2 + 2) + c / (c^2 + 2) is less than or equal to 1.-/
theorem inequalities_70692 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) ≤ 1 := by

  -- Step 1: Use an inequality to bound each term by a simpler expression
  have h1 : a / (a ^ 2 + 2) ≤ a / (2 * a + 1) := by
    -- Show that a² + 2 ≥ 2a + 1 using (a - 1)² ≥ 0
    have h2 : a ^ 2 + 2 ≥ 2 * a + 1 := by
      nlinarith [sq_nonneg (a - 1)]
    apply (div_le_div_iff (by linarith) (by linarith)).mpr
    nlinarith

  have h2 : b / (b ^ 2 + 2) ≤ b / (2 * b + 1) := by
    have h2 : b ^ 2 + 2 ≥ 2 * b + 1 := by
      nlinarith [sq_nonneg (b - 1)]
    apply (div_le_div_iff (by linarith) (by linarith)).mpr
    nlinarith

  have h3 : c / (c ^ 2 + 2) ≤ c / (2 * c + 1) := by
    have h2 : c ^ 2 + 2 ≥ 2 * c + 1 := by
      nlinarith [sq_nonneg (c - 1)]
    apply (div_le_div_iff (by linarith) (by linarith)).mpr
    nlinarith

  -- Step 2: Use AM-GM or related inequalities to get a bound on a + b + c
  have h5 : a + b + c ≥ 3 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  -- Step 3: Show the simplified sum is ≤ 1 using an algebraic identity
  have h7 : a / (2 * a + 1) + b / (2 * b + 1) + c / (2 * c + 1) ≤ 1 := by
    -- Denominator is positive
    have h1 : (2 * a + 1) * (2 * b + 1) * (2 * c + 1) > 0 := by
      apply mul_pos
      apply mul_pos
      all_goals linarith

    -- Combine the three fractions into a single one with common denominator
    have h13 : a / (2 * a + 1) + b / (2 * b + 1) + c / (2 * c + 1) =
      (a * (2 * b + 1) * (2 * c + 1) + b * (2 * a + 1) * (2 * c + 1) + c * (2 * a + 1) * (2 * b + 1)) /
      ((2 * a + 1) * (2 * b + 1) * (2 * c + 1)) := by
      field_simp
      ring

    -- Apply the simplified form and show it's ≤ 1
    rw [h13]
    apply (div_le_one (by linarith)).mpr
    linarith

  -- Final step: Combine all inequalities
  linarith
