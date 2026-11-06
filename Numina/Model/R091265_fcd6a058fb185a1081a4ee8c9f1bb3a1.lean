import Mathlib

open Real

theorem number_theory_5962 :
    ∀ x y : ℝ, x ≤ y → ⌊x⌋ ≤ ⌊y⌋ := by
  intro x y hxy
  exact Int.floor_le_floor hxy