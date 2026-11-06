import Mathlib

theorem algebra_15596 (x : ℝ) :
    ∃ y : ℝ, y^2 = -10 * x^2 - 11 * x + 6 ↔ x ∈ Set.Icc (-3 / 2) (2 / 5) := by
  use √(-10 * x^2 - 11 * x + 6)
  constructor
  · -- Forward direction: If y^2 = -10 * x^2 - 11 * x + 6, then x ∈ Set.Icc (-3 / 2) (2 / 5)
    intro h
    have h1 : -10 * x^2 - 11 * x + 6 ≥ 0 := by
      calc
        -10 * x^2 - 11 * x + 6 = (√(-10 * x^2 - 11 * x + 6))^2 := by rw [h]
        _ ≥ 0 := by positivity
    have h2 : -3 / 2 ≤ x := by nlinarith
    have h3 : x ≤ 2 / 5 := by nlinarith
    exact ⟨h2, h3⟩
  · -- Backward direction: If x ∈ Set.Icc (-3 / 2) (2 / 5), then y^2 = -10 * x^2 - 11 * x + 6
    rintro ⟨h1, h2⟩
    have h3 : -10 * x^2 - 11 * x + 6 ≥ 0 := by nlinarith
    have h4 : (√(-10 * x^2 - 11 * x + 6))^2 = -10 * x^2 - 11 * x + 6 := by
      rw [Real.sq_sqrt]
      all_goals nlinarith
    linarith