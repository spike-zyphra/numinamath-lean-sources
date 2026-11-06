import Mathlib

theorem algebra_2101 :
  Set.ncard {a : ℤ | abs (2 * a + 7) + abs (2 * a - 1) = 8} = 4 := by 
  have h1 : {a : ℤ | abs (2 * a + 7) + abs (2 * a - 1) = 8} = {-3, -2, -1, 0} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume abs (2 * a + 7) + abs (2 * a - 1) = 8, then a ∈ {-3, -2, -1, 0}
      intro h
      have h2 : abs (2 * a + 7) + abs (2 * a - 1) = 8 := h
      by_cases h3 : 2 * a + 7 ≥ 0
      · -- Case where 2a + 7 ≥ 0
        by_cases h4 : 2 * a - 1 ≥ 0
        · -- Both non-negative
          rw [abs_of_nonneg h3, abs_of_nonneg h4] at h2
          omega
        · -- 2a - 1 < 0
          rw [abs_of_nonneg h3, abs_of_neg (lt_of_not_ge h4)] at h2
          omega
      · -- Case where 2a + 7 < 0
        by_cases h4 : 2 * a - 1 ≥ 0
        · -- 2a + 7 < 0, 2a - 1 ≥ 0
          rw [abs_of_neg (lt_of_not_ge h3), abs_of_nonneg h4] at h2
          omega
        · -- Both negative
          rw [abs_of_neg (lt_of_not_ge h3), abs_of_neg (lt_of_not_ge h4)] at h2
          omega
    · -- Assume a ∈ {-3, -2, -1, 0}, then abs (2 * a + 7) + abs (2 * a - 1) = 8
      rintro (rfl | rfl | rfl | rfl)
      · -- a = -3
        norm_num [abs_of_nonneg, abs_of_neg]
      · -- a = -2
        norm_num [abs_of_nonneg, abs_of_neg]
      · -- a = -1
        norm_num [abs_of_nonneg, abs_of_neg]
      · -- a = 0
        norm_num [abs_of_nonneg, abs_of_neg]
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]