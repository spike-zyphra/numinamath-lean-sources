import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_228909 {x y : ℝ} :
  sinh (x + y) = sinh x * cosh y + cosh x * sinh y ∧
  cosh (x + y) = cosh x * cosh y + sinh x * sinh y ∧
  sinh (x - y) = sinh x * cosh y - cosh x * sinh y ∧
  cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
    constructor
    · -- First identity: $\sinh (x + y) = \sinh x \cdot \cosh y + \cosh x \cdot \sinh y$
      rw [sinh_add]
    constructor
    · -- Second identity: $\cosh (x + y) = \cosh x \cdot \cosh y + \sinh x \cdot \sinh y$
      rw [cosh_add]
    constructor
    · -- Third identity: $\sinh (x - y) = \sinh x \cdot \cosh y - \cosh x \cdot \sinh y$
      rw [show sinh (x - y) = sinh (x + (-y)) by ring]
      rw [sinh_add]
      simp [sinh_neg, cosh_neg]
      all_goals ring
    · -- Fourth identity: $\cosh (x - y) = \cosh x \cdot \cosh y - \sinh x \cdot \sinh y$
      rw [show cosh (x - y) = cosh (x + (-y)) by ring]
      rw [cosh_add]
      simp [sinh_neg, cosh_neg]
      all_goals ring