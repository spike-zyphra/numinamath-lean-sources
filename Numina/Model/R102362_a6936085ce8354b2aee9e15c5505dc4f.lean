import Mathlib

theorem number_theory_278662 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 100 ∧ 3 ∣ n ∧ 7 ∣ n} = 4 := by
  have h1 : {n : ℕ | 0 < n ∧ n < 100 ∧ 3 ∣ n ∧ 7 ∣ n} = {21, 42, 63, 84} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      interval_cases n <;> norm_num at *
      <;> tauto
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]