import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_204396 :
  IsGreatest {x | ∃ a b : ℝ, x = 2*a - b ∧ a - b + 1 ≥ 0 ∧ b + 1 ≥ 0 ∧ a + b + 1 ≤ 0} 1 := by
  constructor
  · -- Prove that 1 belongs to the set
    use 0, -1
    norm_num
  · -- Prove that 1 is the greatest element in the set
    intro x h
    rcases h with ⟨a, b, h_eq, h1, h2, h3⟩
    linarith