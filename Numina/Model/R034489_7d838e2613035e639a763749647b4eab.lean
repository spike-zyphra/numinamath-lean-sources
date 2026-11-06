import Mathlib
open Real Set

theorem algebra_9508 :
  IsLeast {u : ℝ | ∃ x y z : ℝ, (0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) ∧ (x = y + z - 1) ∧ (y + z - 1 = 4 - y - 2 * z) ∧ (u = 2 * x ^ 2 - 2 * y + z)} (- 1 / 2) := by
  constructor
  · -- Show that -1/2 is in the set.
    use (3 / 2), (5 / 2), (0)
    constructor
    · -- Show all variables are non-negative
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    constructor
    · -- Show x = y + z - 1
      norm_num
    constructor
    · -- Show y + z - 1 = 4 - y - 2 * z
      norm_num
    · -- Show u = 2 * x ^ 2 - 2 * y + z
      norm_num
  · -- Show that -1/2 is the least element in the set
    intro u h
    rcases h with ⟨x, y, z, h_nonneg, h1, h2, h3⟩
    have h_nonneg_z : 0 ≤ z := h_nonneg.2.2
    have h_nonneg_y : 0 ≤ y := h_nonneg.2.1
    have h_nonneg_x : 0 ≤ x := h_nonneg.1
    have eq1 : y = (5 - 3 * z) / 2 := by
      nlinarith [h1, h2]
    have eq2 : x = (3 - z) / 2 := by
      nlinarith [h1, eq1]
    have h3' : u = (z ^ 2 + 2 * z - 1) / 2 := by 
      rw [h3]
      rw [eq2, eq1]
      nlinarith
    have eq4 : z ^ 2 + 2 * z ≥ 0 := by 
      nlinarith [h_nonneg_z]
    have eq5 : u ≥ -1 / 2 := by
      linarith [h3']
    linarith