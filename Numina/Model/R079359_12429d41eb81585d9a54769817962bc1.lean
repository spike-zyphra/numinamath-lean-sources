import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_303692 :
  IsGreatest {z : ℝ | ∃ x y, z = 2*x + y ∧ x + 1 ≥ 0 ∧ y + 1 ≥ 0 ∧ x - 2*y + 2 ≥ 0 ∧ x + y ≤ 2} 5 ∧
  IsLeast {z : ℝ | ∃ x y, z = 2*x + y ∧ x + 1 ≥ 0 ∧ y + 1 ≥ 0 ∧ x - 2*y + 2 ≥ 0 ∧ x + y ≤ 2} (-3) := by
  constructor
  · -- We need to prove 5 is the greatest element in the set
    constructor
    · -- Show that 5 is in the set by finding the point (3, -1)
      use 3, -1
      norm_num
    · -- Show that any element in the set is ≤ 5
      intro z h
      rcases h with ⟨x, y, h_eq, hx1, hy1, h2, h3⟩
      nlinarith
  · -- We need to prove -3 is the least element in the set
    constructor
    · -- Show that -3 is in the set by finding the point (-1, -1)
      use -1, -1
      norm_num
    · -- Show that any element in the set is ≥ -3
      intro z h
      rcases h with ⟨x, y, h_eq, hx1, hy1, h2, h3⟩
      nlinarith