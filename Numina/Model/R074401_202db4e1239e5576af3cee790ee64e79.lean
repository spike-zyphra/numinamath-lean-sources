import Mathlib

theorem algebra_2637 :
  Set.ncard {x : ℤ | abs (3 * x - 4) + abs (3 * x + 2) = 6} = 2 := by 
  have h1 : {x : ℤ | abs (3 * x - 4) + abs (3 * x + 2) = 6} = {0, 1} := by 
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume abs (3 * x - 4) + abs (3 * x + 2) = 6, prove x ∈ {0, 1}
      intro h
      by_cases h2 : (3 * x - 4) ≥ 0
      · -- Case where 3x - 4 ≥ 0, so x ≥ 4/3
        by_cases h3 : (3 * x + 2) ≥ 0
        · -- Case where both expressions are non-negative
          rw [abs_of_nonneg h2, abs_of_nonneg h3] at h
          omega -- This solves linear integer arithmetic
        · -- Case where 3x + 2 < 0, but 3x - 4 ≥ 0
          rw [abs_of_nonneg h2, abs_of_neg (lt_of_not_ge h3)] at h
          omega -- The solution would be outside the field
      · -- Case where 3x - 4 < 0, so x < 4/3
        by_cases h3 : (3 * x + 2) ≥ 0
        · -- Case where 3x - 4 < 0 and 3x + 2 ≥ 0
          rw [abs_of_neg (lt_of_not_ge h2), abs_of_nonneg h3] at h
          omega -- Possible solutions
        · -- Case where both expressions are negative
          rw [abs_of_neg (lt_of_not_ge h2), abs_of_neg (lt_of_not_ge h3)] at h
          omega -- Possible solutions
    · -- Show that {0, 1} are solutions
      rintro (rfl | rfl)
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }