import Mathlib

theorem algebra_190131 : {x : ℝ | abs (x - 1) = abs (x - 2) + abs (x - 3)}.encard = 2 := by
  have h1 : {x : ℝ | abs (x - 1) = abs (x - 2) + abs (x - 3)} = {2, 4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume abs (x - 1) = abs (x - 2) + abs (x - 3), prove x ∈ {2, 4}
      intro h
      by_cases h1 : x ≥ 3
      · -- x ≥ 3
        rw [abs_of_nonneg (show x - 1 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonneg (show x - 3 ≥ 0 by linarith)] at h
        have h2 : x = 4 := by linarith
        rw [h2]
        norm_num
      by_cases h2 : x ≥ 2
      · -- 2 ≤ x < 3
        rw [abs_of_nonneg (show x - 1 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_neg (show x - 3 < 0 by linarith)] at h
        have h3 : x = 2 := by linarith
        rw [h3]
        norm_num
      by_cases h3 : x ≥ 1
      · -- 1 ≤ x < 2
        rw [abs_of_nonneg (show x - 1 ≥ 0 by linarith), abs_of_neg (show x - 2 < 0 by linarith), abs_of_neg (show x - 3 < 0 by linarith)] at h
        exfalso
        linarith
      · -- x < 1
        rw [abs_of_neg (show x - 1 < 0 by linarith), abs_of_neg (show x - 2 < 0 by linarith), abs_of_neg (show x - 3 < 0 by linarith)] at h
        exfalso
        linarith
    · -- Assume x ∈ {2, 4}, prove abs (x - 1) = abs (x - 2) + abs (x - 3)
      rintro (h | h)
      · -- x = 2
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- x = 4
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_pair]
  all_goals norm_num