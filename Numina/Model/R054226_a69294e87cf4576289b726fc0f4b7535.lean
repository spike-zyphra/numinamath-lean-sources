import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_318212 : IsGreatest {x | ∃ t : ℝ, x = min (min (4 * t + 1) (t + 2)) (-2 * t + 4)} (8 / 3) := by
  constructor
  · -- First part: Show that 8/3 is in the set
    use 2 / 3
    norm_num
  · -- Second part: Show that for all x in the set, x ≤ 8/3
    intro x
    rintro ⟨t, ht⟩
    have h1 : min (min (4 * t + 1) (t + 2)) (-2 * t + 4) ≤ 8 / 3 := by
      by_cases h1 : 4 * t + 1 ≤ t + 2
      · -- Case 1: 4t+1 ≤ t+2, so min(4t+1, t+2) = 4t+1
        have h2 : min (4 * t + 1) (t + 2) = 4 * t + 1 := by
          apply min_eq_left
          linarith
        by_cases h3 : 4 * t + 1 ≤ -2 * t + 4
        · -- Case 1a: 4t+1 ≤ -2t+4, so min(4t+1, -2t+4) = 4t+1
          have h4 : min (min (4 * t + 1) (t + 2)) (-2 * t + 4) = 4 * t + 1 := by
            rw [h2]
            apply min_eq_left
            linarith
          linarith [h4]
        · -- Case 1b: 4t+1 > -2t+4, so min(4t+1, -2t+4) = -2t+4
          have h4 : min (min (4 * t + 1) (t + 2)) (-2 * t + 4) = -2 * t + 4 := by
            rw [h2]
            apply min_eq_right
            linarith
          linarith [h4]
      · -- Case 2: 4t+1 > t+2, so min(4t+1, t+2) = t+2
        have h2 : min (4 * t + 1) (t + 2) = t + 2 := by
          apply min_eq_right
          linarith
        by_cases h3 : t + 2 ≤ -2 * t + 4
        · -- Case 2a: t+2 ≤ -2t+4, so min(t+2, -2t+4) = t+2
          have h4 : min (min (4 * t + 1) (t + 2)) (-2 * t + 4) = t + 2 := by
            rw [h2]
            apply min_eq_left
            linarith
          linarith [h4]
        · -- Case 2b: t+2 > -2t+4, so min(t+2, -2t+4) = -2t+4
          have h4 : min (min (4 * t + 1) (t + 2)) (-2 * t + 4) = -2 * t + 4 := by
            rw [h2]
            apply min_eq_right
            linarith
          linarith [h4]
    linarith [ht, h1]