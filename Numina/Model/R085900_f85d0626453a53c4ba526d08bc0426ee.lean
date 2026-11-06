import Mathlib

theorem algebra_133216 (x y z : ℝ) :
    (x - 8) / -3 = (y - 6) / -2 ∧ (y - 6) / -2 = z / -1 ↔
    x - y - z - 2 = 0 ∧ x - 2 * y + z + 4 = 0 := by
  constructor
  · -- Assume the equality of the ratios and prove the plane equations
    rintro ⟨h₁, h₂⟩
    constructor
    · -- Proving the first plane equation
      linarith
    · -- Proving the second plane equation
      linarith
  · -- Assume the plane equations and prove the equality of the ratios
    rintro ⟨h₁, h₂⟩
    constructor
    · -- First ratio equality
      field_simp at *
      linarith
    · -- Second ratio equality
      field_simp at *
      linarith