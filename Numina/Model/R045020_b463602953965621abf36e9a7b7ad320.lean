import Mathlib

theorem algebra_3687 : ∑ᶠ (x : ℝ) (h : abs (x - 8) + abs (x - 5) = 11), x = 13 := by
  have h1 : {x : ℝ | abs (x - 8) + abs (x - 5) = 11} = {1, 12} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume abs (x - 8) + abs (x - 5) = 11, prove x ∈ {1, 12}
      intro h
      by_cases h2 : x ≥ 8
      · -- x ≥ 8
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
        have h3 : x = 12 := by
          nlinarith
        simp [h3]
      by_cases h3 : x ≥ 5
      · -- 5 ≤ x < 8
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
        linarith
      · -- x < 5
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
        have h4 : x = 1 := by
          nlinarith
        simp [h4]
    · -- Assume x ∈ {1, 12}, prove abs (x - 8) + abs (x - 5) = 11
      rintro (rfl | rfl)
      · -- x = 1
        norm_num [abs]
      · -- x = 12
        norm_num [abs]
  rw [show ∑ᶠ (x : ℝ) (h : abs (x - 8) + abs (x - 5) = 11), x = ∑ᶠ (x : ℝ) (h : x ∈ {x : ℝ | abs (x - 8) + abs (x - 5) = 11}), x by simp]
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num