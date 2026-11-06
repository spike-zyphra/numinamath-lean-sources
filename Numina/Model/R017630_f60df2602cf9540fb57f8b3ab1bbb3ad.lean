import Mathlib

open Real

theorem inequalities_7129 (x : ℝ) : 0 ≤ (x % 1) ∧ (x % 1) < 1 := by
  constructor
  · -- Show 0 ≤ x % 1
    have h1 : 0 ≤ x % 1 := by
      norm_num [Int.floor_le]
    exact h1
  · -- Show x % 1 < 1
    have h2 : x % 1 < 1 := by
      norm_num [Int.lt_floor_add_one]
    exact h2