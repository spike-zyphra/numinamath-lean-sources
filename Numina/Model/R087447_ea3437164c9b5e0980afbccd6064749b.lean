import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_309289 :
  IsGreatest {z : ℝ | ∃ x y, z = 2*x + y ∧ x + 2*y ≤ 3 ∧ x ≥ 0 ∧ y ≥ 0} 6 := by
  constructor
  · -- Let's find values for x and y such that $2x + y = 6$ and all constraints are satisfied.
    use 3, 0
    norm_num
  · -- Now we need to prove that no value greater than 6 belongs to the set.
    intro z h
    rcases h with ⟨x, y, h_eq, h1, h2, h3⟩
    linarith