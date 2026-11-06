import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_182345 :
  {x : ℝ | x + 2 < 3 + 2 * x ∧ 4 * x - 3 < 3 * x - 1 ∧ 8 + 5 * x ≥ 6 * x + 7} = Ioc (-1) 1 := by
  ext x
  simp only [mem_setOf_eq, mem_Ioc]
  constructor
  · -- First, we show that if x satisfies the system of inequalities, then x ∈ (-1, 1].
    intro h
    rcases h with ⟨h1, h2, h3⟩
    constructor
    · -- Show that x > -1
      linarith
    · -- Show that x ≤ 1
      linarith
  · -- Now, we show the reverse. If x ∈ (-1, 1], then it satisfies all three inequalities.
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that x + 2 < 3 + 2x
      linarith
    constructor
    · -- Show that 4x - 3 < 3x - 1
      linarith
    · -- Show that 8 + 5x ≥ 6x + 7
      linarith