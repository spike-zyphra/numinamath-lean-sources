import Mathlib

theorem algebra_9164 (x : ℝ) : (x^2 - 3 * x + 2) * (x^2 + 3 * x - 2) = x^2 * (x + 3) * (x - 3) ↔ x = 1 / 3 := by
  constructor
  · -- Forward direction: If the equation holds, then x =1/3
    intro h
    have eq1 : (x^2 - 3 * x + 2) * (x^2 + 3 * x - 2) = x^2 * (x + 3) * (x - 3) := h
    have eq2 : (x^2 - 3 * x + 2) * (x^2 + 3 * x - 2) = x^4 - 9 * x^2 + 12 * x - 4 := by
      ring
    have eq3 : x^2 * (x + 3) * (x - 3) = x^4 - 9 * x^2 := by
      ring
    rw [eq2, eq3] at eq1
    -- Subtracting the right side from the left side yields 12x -4 =0
    have eq4 : 12 * x - 4 = 0 := by
      linarith
    linarith
  · -- Backward direction: If x =1/3, then the equation holds
    intro h
    rw [h]
    norm_num