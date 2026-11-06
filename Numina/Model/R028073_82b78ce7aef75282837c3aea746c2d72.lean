import Mathlib

theorem algebra_158266 (A : Set ℝ) (hA : A = {x | x > 0}) :
    {x | x ∈ A ∧ x^2 > 1} = {x | 1 < x} := by
  rw [hA]
  ext x
  simp only [Set.mem_setOf_eq, and_imp]
  constructor
  · -- Assume x > 0 and x² > 1, prove x > 1
    intro h
    rcases h with ⟨hx1, hx2⟩
    nlinarith
  · -- Assume x > 1, prove x > 0 and x² > 1
    intro h
    constructor
    · -- Show x > 0
      linarith
    · -- Show x² > 1
      nlinarith
  all_goals linarith