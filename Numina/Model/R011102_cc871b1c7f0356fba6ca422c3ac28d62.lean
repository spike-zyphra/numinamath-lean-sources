import Mathlib

open Real Set

theorem calculus_7736 : ∀ x : ℝ, abs (sin x) ≤ abs x := by
  intro x
  apply abs_sin_le_abs