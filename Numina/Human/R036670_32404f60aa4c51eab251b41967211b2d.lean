import Mathlib

open Real Set
open scoped Real

theorem calculus_12463 : arcsin (1 / sqrt 2) = π / 4 := by
  have h1 : arcsin (1 / sqrt 2) = π / 4 := by
    have h1 : sin (π / 4) = 1 / sqrt 2 := by
      field_simp [sin_pi_div_four]
    rw [←h1]
    apply arcsin_sin
    all_goals linarith [Real.pi_pos]
  exact h1