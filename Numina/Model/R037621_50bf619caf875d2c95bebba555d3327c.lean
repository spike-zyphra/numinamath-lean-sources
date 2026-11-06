import Mathlib

theorem algebra_19921 : {n : ℤ | ∃ k, n = -36 + 7 * k ∧ k ≥ 0 ∧ k ≤ 12}.encard = 13 := by
  have h : {n : ℤ | ∃ k, n = -36 + 7 * k ∧ k ≥ 0 ∧ k ≤ 12} = {-36, -29, -22, -15, -8, -1, 6, 13, 20, 27, 34, 41, 48} := by 
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor 
    · -- Assume n in the set 
      rintro ⟨k, h1, hk1, hk2⟩ 
      have h2 : k ≤ 12 := by linarith 
      have h3 : k ≥ 0 := by linarith 
      interval_cases k <;> omega 
    · -- Assume n in the explicit set 
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · refine ⟨0, by norm_num, by norm_num, by norm_num⟩
      · refine ⟨1, by norm_num, by norm_num, by norm_num⟩
      · refine ⟨2, by norm_num, by norm_num, by norm_num⟩ 
      · refine ⟨3, by norm_num, by norm_num, by norm_num⟩ 
      · refine ⟨4, by norm_num, by norm_num, by norm_num⟩ 
      · refine ⟨5, by norm_num, by norm_num, by norm_num⟩ 
      · refine ⟨6, by norm_num, by norm_num, by norm_num⟩ 
      · refine ⟨7, by norm_num, by norm_num, by norm_num⟩ 
      · refine ⟨8, by norm_num, by norm_num, by norm_num⟩ 
      · refine ⟨9, by norm_num, by norm_num, by norm_num⟩ 
      · refine ⟨10, by norm_num, by norm_num, by norm_num⟩ 
      · refine ⟨11, by norm_num, by norm_num, by norm_num⟩ 
      · refine ⟨12, by norm_num, by norm_num, by norm_num⟩ 
  rw [h]
  rw [Set.encard]
  simp [Set.ncard]