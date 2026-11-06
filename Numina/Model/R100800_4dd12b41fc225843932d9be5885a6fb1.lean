import Mathlib

theorem algebra_2644 :
  IsGreatest {x | ∃ a : ℝ, 0 ≤ a ∧ a ≤ 4 ∧ x = |a - 2| + |3 - a|} 5 := by
  constructor
  · -- Show that 5 belongs to the set, meaning there exists an a in [0,4] such that |a-2| + |3-a| = 5
    use 0
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Show that for any value in the set, it cannot exceed 5
    intro x hx
    rcases hx with ⟨a, ha1, ha2, h_eq⟩
    by_cases h1 : a ≥ 3
    · -- Case where a ≥ 3
      rw [h_eq]
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · -- Case where a < 3
      by_cases h2 : a ≥ 2
      · -- Case where 2 ≤ a < 3
        rw [h_eq]
        rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
        linarith
      · -- Case where a < 2
        rw [h_eq]
        rw [abs_of_nonpos (by linarith), abs_of_pos (by linarith)]
        linarith