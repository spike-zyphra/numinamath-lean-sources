import Mathlib

theorem algebra_12365 : Set.ncard {x : ℝ | abs (x - 1) = abs (x - 2) + abs (x - 3)} = 2 := by
  have h1 : {x : ℝ | abs (x - 1) = abs (x - 2) + abs (x - 3)} = {2, 4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
              and_imp]
    constructor
    · -- Assume abs (x - 1) = abs (x - 2) + abs (x - 3)
      intro h
      by_cases h1 : x ≥ 3
      · -- Case x ≥ 3
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
        have h2 : x = 4 := by linarith
        right
        exact h2
      · -- Case x < 3
        by_cases h2 : x ≥ 2
        · -- Case 2 ≤ x < 3
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith)] at h
          have h3 : x = 2 := by linarith
          left
          exact h3
        · -- Case x < 2
          by_cases h3 : x ≥ 1
          · -- Case 1 ≤ x < 2
            rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)] at h
            linarith -- contradiction
          · -- Case x < 1
            rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)] at h
            linarith -- contradiction
    · -- Show that if x ∈ {2, 4}, then abs (x - 1) = abs (x - 2) + abs (x - 3)
      rintro (h | h)
      · -- x = 2
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- x = 4
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]