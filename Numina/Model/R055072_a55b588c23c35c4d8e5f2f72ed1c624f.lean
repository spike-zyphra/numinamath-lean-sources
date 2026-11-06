import Mathlib

theorem algebra_22508 (x y : ℝ) : (x / 2 - 3)^2 + y^2 = 10 ↔
    (x - 6)^2 / 4 + y^2 = 10 := by
  constructor
  · -- Assume left side: (x / 2 - 3)^2 + y^2 = 10, prove right side: (x - 6)^2 / 4 + y^2 = 10
    intro h
    have h1 : (x / 2 - 3) ^ 2 + y^2 = 10 := h
    have h2 : (x / 2 - 3) ^ 2 = (x - 6) ^ 2 / 4 := by
      ring
    rw [h2] at h1
    linarith
  · -- Assume right side: (x - 6)^2 / 4 + y^2 = 10, prove left side: (x / 2 - 3)^2 + y^2 = 10
    intro h
    have h1 : (x - 6) ^ 2 / 4 + y^2 = 10 := h
    have h2 : (x / 2 - 3) ^ 2 = (x - 6) ^ 2 / 4 := by
      ring
    have h3 : (x / 2 - 3) ^ 2 + y^2 = 10 := by
      linarith [h1, h2]
    linarith