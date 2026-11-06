import Mathlib

theorem algebra_131855 (a b c : ℚ) (habc : b ≠ c ∧ c ≠ a ∧ a ≠ b) :
    IsSquare (1/(b - c)^2 + 1/(c - a)^2 + 1/(a - b)^2) := by

  rcases habc with ⟨hbne, hcne, hane⟩
  use (1/(b - c) + 1/(c - a) + 1/(a - b))
  have h1 : b - c ≠ 0 := by
    intro h
    apply hbne
    linarith
  have h2 : c - a ≠ 0 := by
    intro h
    apply hcne
    linarith
  have h3 : a - b ≠ 0 := by
    intro h
    apply hane
    linarith
  field_simp [(show b - c ≠ 0 by assumption), (show c - a ≠ 0 by assumption), (show a - b ≠ 0 by assumption)]
  <;> ring