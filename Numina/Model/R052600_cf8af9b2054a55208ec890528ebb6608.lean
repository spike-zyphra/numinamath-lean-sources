import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_218552 :
  {x : ℝ | abs (1 + x + x^2 / 2) < 1} = {x | -2 < x ∧ x < 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
    constructor
    · -- First, we'll prove that if |1 + x + x^2/2| < 1, then -2 < x < 0.
      intro h
      have h1 : -1 < (1 + x + x^2 / 2) := by linarith [abs_lt.mp h]
      have h2 : (1 + x + x^2 / 2) < 1 := by linarith [abs_lt.mp h]
      constructor
      · -- Show that -2 < x
        nlinarith
      · -- Show that x < 0
        nlinarith
    · -- Now prove the reverse: if -2 < x < 0, then |1 + x + x^2/2| < 1
      rintro ⟨h1, h2⟩
      have h3 : (1 + x + x^2 / 2) < 1 := by
        nlinarith
      have h4 : -1 < (1 + x + x^2 / 2) := by
        nlinarith [sq_nonneg (x + 1)]
      apply abs_lt.mpr
      constructor <;> linarith