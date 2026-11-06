import Mathlib

theorem algebra_12201 :
    Set.ncard {n : ℕ | 1000 < n ∧ n < 2000 ∧ 15 ∣ n ∧ 20 ∣ n ∧ 25 ∣ n} = 3 := by
  have h1 : {n : ℕ | 1000 < n ∧ n < 2000 ∧ 15 ∣ n ∧ 20 ∣ n ∧ 25 ∣ n} = {1200, 1500, 1800} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n is in the original set
      intro h
      rcases h with ⟨h1, h2, h3, h4, h5⟩
      interval_cases n <;> norm_num at *
    · -- Show that 1200, 1500, 1800 satisfy the original conditions.
      rintro (rfl | rfl | rfl)
      · -- Show that 1200 is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show that 1500 is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show that 1800 is in the set
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]