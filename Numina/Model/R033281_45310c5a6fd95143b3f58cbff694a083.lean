import Mathlib

theorem number_theory_289409 : {n : ℕ | ∃ k, n = k^2 ∧ n ∈ Finset.Icc 2 150}.encard = 11 := by 
  have h1 : {n : ℕ | ∃ k, n = k^2 ∧ n ∈ Finset.Icc 2 150} = 
    {4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
      Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is in the left side, prove it's in the right
      rintro ⟨k, rfl, hk1, hk2⟩
      have h2 : k ≤ 12 := by nlinarith
      interval_cases k <;> norm_num at *
    · -- Assume n is in the right side, prove it's in the left
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- 4
        exact ⟨2, by norm_num, by norm_num⟩
      · -- 9
        exact ⟨3, by norm_num, by norm_num⟩
      · -- 16
        exact ⟨4, by norm_num, by norm_num⟩
      · -- 25
        exact ⟨5, by norm_num, by norm_num⟩
      · -- 36
        exact ⟨6, by norm_num, by norm_num⟩
      · -- 49
        exact ⟨7, by norm_num, by norm_num⟩
      · -- 64
        exact ⟨8, by norm_num, by norm_num⟩
      · -- 81
        exact ⟨9, by norm_num, by norm_num⟩
      · -- 100
        exact ⟨10, by norm_num, by norm_num⟩
      · -- 121
        exact ⟨11, by norm_num, by norm_num⟩
      · -- 144
        exact ⟨12, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { rfl }