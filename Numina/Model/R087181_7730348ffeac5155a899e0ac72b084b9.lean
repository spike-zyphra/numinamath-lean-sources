import Mathlib

theorem algebra_2621 {x : ℝ} (hx : x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1) :
    ∃ y, y = 1 / ((1 - abs x) / abs x) := by 
  refine ⟨1 / ((1 - abs x) / abs x), rfl⟩