import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_316145 :
  IsGreatest {x | ∃ y : ℝ, x = min (min (2 * y + 1) (y + 2)) (-y + 6)} 4 := by
  constructor
  · -- Show that 4 is in the set, achieved when y = 2
    use 2
    norm_num
  · -- Show that 4 is an upper bound
    intro x hx
    rcases hx with ⟨y, hy⟩
    rw [hy]
    -- We analyze the min functions by cases
    by_cases h1 : 2 * y + 1 ≤ y + 2
    · -- Case 1: 2y+1 ≤ y+2 (i.e., y ≤ 1)
      have h1' : min (2 * y + 1) (y + 2) = 2 * y + 1 := by apply min_eq_left h1
      rw [h1']
      by_cases h2 : 2 * y + 1 ≤ -y + 6
      · -- Subcase 1a: 2y+1 ≤ -y+6
        have h2' : min (2 * y + 1) (-y + 6) = 2 * y + 1 := by apply min_eq_left h2
        rw [h2']
        linarith
      · -- Subcase 1b: 2y+1 > -y+6
        have h2' : min (2 * y + 1) (-y + 6) = -y + 6 := by apply min_eq_right (le_of_not_le h2)
        rw [h2']
        linarith
    · -- Case 2: 2y+1 > y+2 (i.e., y > 1)
      have h1' : min (2 * y + 1) (y + 2) = y + 2 := by apply min_eq_right (le_of_not_le h1)
      rw [h1']
      by_cases h2 : y + 2 ≤ -y + 6
      · -- Subcase 2a: y+2 ≤ -y+6
        have h2' : min (y + 2) (-y + 6) = y + 2 := by apply min_eq_left h2
        rw [h2']
        linarith
      · -- Subcase 2b: y+2 > -y+6
        have h2' : min (y + 2) (-y + 6) = -y + 6 := by apply min_eq_right (le_of_not_le h2)
        rw [h2']
        linarith