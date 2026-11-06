import Mathlib

theorem number_theory_3675 : {n : ℕ | 1000 < n ∧ n < 2000 ∧ 15 ∣ n ∧ 20 ∣ n ∧ 25 ∣ n}.encard = 3 := by
  have h1 : {n : ℕ | 1000 < n ∧ n < 2000 ∧ 15 ∣ n ∧ 20 ∣ n ∧ 25 ∣ n} = {1200, 1500, 1800} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n satisfies the conditions
      intro h
      rcases h with ⟨h1000, h2000, h15, h20, h25⟩
      interval_cases n <;> norm_num at *
      <;> omega
    · -- Assume n ∈ {1200, 1500, 1800}
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
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { all_goals omega }