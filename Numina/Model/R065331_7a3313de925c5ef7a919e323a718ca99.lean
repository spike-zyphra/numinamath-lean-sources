import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_319245 (a b : ℝ)
  (h₀ : a + b - 2 ≥ 0) (h₁ : b - a - 1 ≤ 0) (h₂ : a ≤ 1) :
  (a + 2 * b) / (2 * a + b) ≤ 7 / 5 := by
  have h5 : 2 * a + b > 0 := by
    nlinarith
  have h4 : a + 2 * b ≤ (7 / 5) * (2 * a + b) := by
    nlinarith
  have h6 : (a + 2 * b) / (2 * a + b) ≤ ( (7 / 5) * (2 * a + b) ) / (2 * a + b) := by
    apply (div_le_div_right h5).mpr
    nlinarith
  have h10 : ( (7 / 5) * (2 * a + b) ) / (2 * a + b) = (7 / 5) := by
    field_simp [show 2 * a + b ≠ 0 from by nlinarith]
    <;> nlinarith
  linarith [h6, h10]