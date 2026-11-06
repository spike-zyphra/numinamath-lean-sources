import Mathlib

theorem number_theory_281104 (n : ℕ) (hn : n = 18) :
    {k | ∃ m, k = m * 4 ∧ k ≤ n}.encard ≤ 5 := by
  rw [hn]
  have h1 : {k | ∃ m, k = m * 4 ∧ k ≤ 18} = {0, 4, 8, 12, 16} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume k ∈ {k | ∃ m, k = m * 4 ∧ k ≤ 18}, prove k ∈ {0, 4, 8, 12, 16}
      rintro ⟨m, rfl, hm⟩
      have h2 : m ≤ 4 := by
        omega
      interval_cases m <;> tauto
    · -- Assume k ∈ {0, 4, 8, 12, 16}, prove k ∈ {k | ∃ m, k = m * 4 ∧ k ≤ 18}
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- k = 0
        exact ⟨0, by norm_num, by norm_num⟩
      · -- k = 4
        exact ⟨1, by norm_num, by norm_num⟩
      · -- k = 8
        exact ⟨2, by norm_num, by norm_num⟩
      · -- k = 12
        exact ⟨3, by norm_num, by norm_num⟩
      · -- k = 16
        exact ⟨4, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals norm_num