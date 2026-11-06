import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_22826 : arccos (-1) = π := by
  have h : arccos (-1) = π := by
    rw [Real.arccos_neg]
    have h1 : arccos 1 = 0 := by
      rw [Real.arccos_one]
    simp [h1]
  exact h