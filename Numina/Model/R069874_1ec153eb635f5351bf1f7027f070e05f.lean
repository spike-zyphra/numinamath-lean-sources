import Mathlib

theorem algebra_102085 {x1 x2 : ℝ} (hx1 : (x1 - 2)^2 = 3 * (x1 + 5)) (hx2 : (x2 - 2)^2 = 3 * (x2 + 5))
    (hx12 : x1 ≠ x2) : x1 * x2 + x1^2 + x2^2 = 60 := by
  -- convert the equation to standard quadratic form
  have h1 : x1^2 - 7 * x1 - 11 = 0 := by
    nlinarith
  have h2 : x2^2 - 7 * x2 - 11 = 0 := by
    nlinarith
  -- Calculate x1 + x2 using the formula (x1^2 - x2^2) = 7*(x1 - x2)
  have h3 : x1 + x2 = 7 := by
    -- Subtracting the two quadratic equations
    have eq1 : x1^2 - x2^2 = 7 * (x1 - x2) := by
      nlinarith [h1, h2]
    have eq2 : x1^2 - x2^2 = (x1 + x2) * (x1 - x2) := by
      ring
    have neq : x1 - x2 ≠ 0 := by
      intro h
      apply hx12
      linarith
    have eq3 : (x1 + x2) * (x1 - x2) = 7 * (x1 - x2) := by
      linarith [eq1, eq2]
    -- From the cancellation of non-zero factor
    have eq4 : x1 + x2 = 7 := by
      apply (mul_right_inj' neq).mp
      linarith
    exact eq4
  -- Calculate the product x1 * x2
  have h4 : x1 * x2 = -11 := by
    nlinarith [h1, h2, h3]
  -- Calculate x1^2 + x2^2
  have h5 : x1^2 + x2^2 = 71 := by
    nlinarith [h1, h2, h3]
  -- Final calculation
  nlinarith [h4, h5]