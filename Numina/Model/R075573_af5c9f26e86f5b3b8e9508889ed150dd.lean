import Mathlib

theorem number_theory_30258 :
    Set.ncard {n : ℕ | 1000 ≤ n ∧ n < 2000 ∧ 15 ∣ n ∧ 20 ∣ n ∧ 25 ∣ n} = 3 := by 
  have h1 : {n : ℕ | 1000 ≤ n ∧ n < 2000 ∧ 15 ∣ n ∧ 20 ∣ n ∧ 25 ∣ n} = {1200, 1500, 1800} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- Show that if n satisfies the divisibility conditions and size constraints, it is one of the three numbers
      intros h
      rcases h with ⟨h1, h2, h3, h4, h5⟩
      interval_cases n <;> omega
    · -- Show that each of 1200, 1500, 1800 satisfies the divisibility conditions and size constraints
      rintro (rfl | rfl | rfl)
      · -- Verify for 1200
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Verify for 1500
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Verify for 1800
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