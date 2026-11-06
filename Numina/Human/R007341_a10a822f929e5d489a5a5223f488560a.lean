import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_182345 :
  {x : ℝ | x + 2 < 3 + 2 * x ∧ 4 * x - 3 < 3 * x - 1 ∧ 8 + 5 * x ≥ 6 * x + 7} = Ioc (-1) 1 := by
  ext x
  simp only [mem_Ioc]
  constructor
  · intro ⟨h1, h2, h3⟩
    have h1' : -1 < x := by linarith
    have h2' : x < 2 := by linarith
    have h3' : x ≤ 1 := by linarith
    exact ⟨h1', h3'⟩
  · intro ⟨h1, h2⟩
    constructor
    · linarith
    · constructor
      · linarith
      · linarith