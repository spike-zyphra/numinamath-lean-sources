import Mathlib

theorem number_theory_295507 :
    Set.ncard {n : ℕ | 8 ∣ n ∧ 50 ∣ n ∧ n ∣ 10000} = 6 := by

  have h1 : {n : ℕ | 8 ∣ n ∧ 50 ∣ n ∧ n ∣ 10000} = {200, 400, 1000, 2000, 5000, 10000} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is in the set
      rintro ⟨h1, h2, h3⟩
      have h4 : n ≤ 10000 := by exact Nat.le_of_dvd (by norm_num) h3
      interval_cases n <;> tauto
    · -- Assume n is in the finite set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show it's in the original set
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- n = 400
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- n = 1000
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- n = 2000
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- n = 5000
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- n = 10000
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]