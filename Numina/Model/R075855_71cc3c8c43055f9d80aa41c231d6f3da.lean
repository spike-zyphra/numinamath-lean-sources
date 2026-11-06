import Mathlib

theorem number_theory_267113 :
  Set.ncard {n : ℕ | 100 ≤ n ∧ n < 300 ∧ 5 ∣ n ∧ 7 ∣ n ∧ ¬10 ∣ n} = 3 := by 
  have h1 : {n : ℕ | 100 ≤ n ∧ n < 300 ∧ 5 ∣ n ∧ 7 ∣ n ∧ ¬10 ∣ n} = {105, 175, 245} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n satisfies the conditions, prove n ∈ {105, 175, 245}
      rintro ⟨h1, h2, h3, h4, h5⟩
      interval_cases n <;> tauto
    · -- Assume n ∈ {105, 175, 245}, prove n satisfies the conditions
      rintro (rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
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