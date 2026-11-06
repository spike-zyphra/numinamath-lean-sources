import Mathlib

theorem inequalities_237864 (x y z : ℝ) (h : x + 3 * y + 2 * z = 6) :
    x^2 + 9 * y^2 - 2 * x - 6 * y + 4 * z ≤ 8 ↔
    (3 - 1 / 2 * x - 3 / 2 * y = z ∧ (x - 2)^2 + (3 * y - 2)^2 ≤ 4) := by
  constructor
  · -- Assume left to right
    intro h1
    have hz : z = 3 - 1 / 2 * x - 3 / 2 * y := by
      linarith
    constructor
    · -- Show that z is expressed in terms of x and y
      linarith
    · -- Show that (x - 2)^2 + (3 * y - 2)^2 ≤ 4
      rw [show z = 3 - 1 / 2 * x - 3 / 2 * y by linarith [hz]] at h1
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2 / 3), sq_nonneg (3 * y - 2)]
  · -- Assume right to left
    rintro ⟨hz, h2⟩
    rw [show z = 3 - 1 / 2 * x - 3 / 2 * y by linarith [hz]]
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2 / 3), sq_nonneg (3 * y - 2)]