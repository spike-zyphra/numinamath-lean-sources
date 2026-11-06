import Mathlib

theorem algebra_95037 : Set.ncard {x : ℝ | abs (x - abs (2 * x + 1)) = 3} = 2 := by
  have h : {x : ℝ | abs (x - abs (2 * x + 1)) = 3} = {-4/3, 2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Forward direction: If abs (x - abs (2 * x + 1)) = 3, then x = -4/3 or 2
      intro h_eq
      cases eq_or_eq_neg_of_abs_eq h_eq with
      | inl h1 =>
        -- Case 1: x - abs (2 * x + 1) = 3
        by_cases h2 : 2 * x + 1 ≥ 0
        · -- Subcase 1a: 2 * x + 1 ≥ 0 (i.e., x ≥ -1/2)
          rw [abs_of_nonneg h2] at h1
          have h3 : x = -4 := by linarith
          linarith
        · -- Subcase 1b: 2 * x + 1 < 0 (i.e., x < -1/2)
          rw [abs_of_neg (lt_of_not_ge h2)] at h1
          have h3 : 3 * x = 2 := by linarith
          have h4 : x ≥ -1 / 2 := by linarith
          linarith
      | inr h2 =>
        -- Case 2: x - abs (2 * x + 1) = -3
        by_cases h3 : 2 * x + 1 ≥ 0
        · -- Subcase 2a: 2 * x + 1 ≥ 0 (i.e., x ≥ -1/2)
          rw [abs_of_nonneg h3] at h2
          have h4 : x = 2 := by linarith
          right
          exact h4
        · -- Subcase 2b: 2 * x + 1 < 0 (i.e., x < -1/2)
          rw [abs_of_neg (lt_of_not_ge h3)] at h2
          have h4 : 3 * x = -4 := by linarith
          have h5 : x = -4 / 3 := by linarith
          left
          exact h5
    · -- Backward direction: If x = -4/3 or 2, then abs (x - abs (2 * x + 1)) = 3
      rintro (h_eq | h_eq)
      · -- Case: x = -4/3
        rw [h_eq]
        norm_num [abs_of_nonneg, abs_of_neg]
      · -- Case: x = 2
        rw [h_eq]
        norm_num [abs_of_nonneg, abs_of_neg]
  rw [h]
  rw [Set.ncard_pair]
  norm_num
  all_goals norm_num