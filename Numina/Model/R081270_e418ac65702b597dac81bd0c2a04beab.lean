import Mathlib

theorem algebra_3247 (x : ℝ) (hx : x ≠ 1 / 2) : -2 * x / (1 - 2 * x) = -3 * (1 - x) / (3 * x - 2) ↔ x = (3 / 5) := by
  constructor
  · -- Forward direction: If the equation holds, then x = 3/5
    intro h

    -- We need to ensure the denominators are non-zero
    have h1 : 1 - 2 * x ≠ 0 := by
      intro h2
      apply hx
      linarith

    -- Check that 3x - 2 ≠ 0
    have h2 : 3 * x - 2 ≠ 0 := by
      by_contra h3
      have h3x : x = 2 / 3 := by linarith

      rw [h3x] at h
      norm_num at h

    -- Now clear fractions and solve
    have h3 : -2 * x / (1 - 2 * x) = -3 * (1 - x) / (3 * x - 2) := h

    -- Multiply both sides by denominators to clear fractions
    field_simp [h1, h2] at h3

    -- We have the polynomial equation
    -- -2 * x * (3 * x - 2) = -3 * (1 - x) * (1 - 2 * x)
    -- Expanding both sides:
    -- Left side: -6 * x^2 + 4 * x
    -- Right side: -3 + 9 * x - 6 * x^2
    -- Simplify to get x = 3/5
    nlinarith

  · -- Backward direction: If x = 3/5, then the equation holds
    intro h
    rw [h]

    -- Check both sides of the equation
    norm_num