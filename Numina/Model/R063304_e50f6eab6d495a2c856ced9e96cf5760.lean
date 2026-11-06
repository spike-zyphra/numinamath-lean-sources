import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_120306 (a : ℝ) (ha : 0 < a) :
    ∃ V, V = (π * (a / 2)^2) * (π * (a / 2)^2) := by
  refine' ⟨(π * (a / 2)^2) * (π * (a / 2)^2), rfl⟩