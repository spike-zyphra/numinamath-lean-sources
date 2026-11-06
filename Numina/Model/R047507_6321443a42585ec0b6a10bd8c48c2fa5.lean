import Mathlib

theorem Other_3764 :
  ∃ x₁ y, x₁ ≠ 1 ∧ y ≠ 1 ∧ x₁ * y = (((5 ^ (125 : ℕ) - 1) / (5 ^ (25 : ℕ) - 1)) : ℕ) := by
  let x₁ := ((5 ^ 50 : ℕ) - 5 ^ 38 + 3 * 5 ^ 25 + 1 - 5 ^ 13)
  let y := ((5 ^ 50 : ℕ) + 5 ^ 38 + 3 * 5 ^ 25 + 1 + 5 ^ 13)
  use x₁, y
  constructor
  · -- Show that x₁ ≠ 1
    norm_num [x₁]
  constructor
  · -- Show that y ≠ 1
    norm_num [y]
  · -- Show that x₁ * y = N
    norm_num [x₁, y]