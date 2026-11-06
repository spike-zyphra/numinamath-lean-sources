import Mathlib

open Real

theorem inequalities_62979 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    x^2 / (1 - x) + (1 - x)^2 / x ≥ 1 := by
  have hx1 : 0 < x := hx.1
  have hx2 : x < 1 := hx.2
  have hx3 : 0 < 1 - x := by linarith
  have h4 : 0 < x * (1 - x) := by
    apply mul_pos
    all_goals linarith
  have h5 : x^2 / (1 - x) + (1 - x)^2 / x - 1 ≥ 0 := by
    have pos1 : 0 < x * (1 - x) := h4
    have pos2 : 0 < x := hx1
    have pos3 : 0 < 1 - x := hx3
    have eq1 : x^2 / (1 - x) + (1 - x)^2 / x - 1 =
        (x^2 * x + (1 - x)^2 * (1 - x) - x * (1 - x)) / (x * (1 - x)) := by
      field_simp [(show (1 - x) ≠ 0 by linarith), (show x ≠ 0 by linarith)]
      <;> ring
    rw [eq1] at *
    apply div_nonneg
    · -- Show the numerator is non-negative
      have eq2 : x^2 * x + (1 - x)^2 * (1 - x) - x * (1 - x) = (2 * x - 1) ^ 2 := by
        nlinarith [sq_nonneg (x - 1 / 2)]
      rw [eq2]
      nlinarith [sq_nonneg (2 * x - 1)]
    · -- Show the denominator is positive
      positivity
  linarith