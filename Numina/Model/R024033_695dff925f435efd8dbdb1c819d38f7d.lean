import Mathlib

theorem inequalities_599014 (x y z a : ℝ) (h : x + y + z = a) :
    x^2 + y^2 + z^2 ≥ a^2 / 3 := by
  have h1 : x + y + z = a := h

  have h2 : 3 * (x^2 + y^2 + z^2) ≥ (x + y + z)^2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

  have h3 : (x + y + z)^2 = a^2 := by
    rw [show x + y + z = a by linarith [h]]

  have h4 : 3 * (x^2 + y^2 + z^2) ≥ a^2 := by
    nlinarith [h2, h3]

  linarith