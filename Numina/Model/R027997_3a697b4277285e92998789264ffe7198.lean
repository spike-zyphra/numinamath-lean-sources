import Mathlib

theorem algebra_308882 : {n | ∃ k, n = 13 + 3 * k ∧ 13 ≤ n ∧ n ≤ 73}.encard = 21 := by
  have h : {n | ∃ k, n = 13 + 3 * k ∧ 13 ≤ n ∧ n ≤ 73} = {13, 16, 19, 22, 25, 28, 31, 34, 37, 40, 43, 46, 49, 52, 55, 58, 61, 64, 67, 70, 73} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: if n is in the left side, it's in the right
      rintro ⟨k, h_eq, hn1, hn2⟩
      rw [h_eq] at *
      have h1 : 0 ≤ k := by
        omega
      have h2 : k ≤ 20 := by
        omega
      interval_cases k <;> norm_num at h_eq hn1 hn2 ⊢ <;> tauto
    · -- Second direction: if n is in the right side, it's in the left
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 13
        refine ⟨0, by norm_num, by norm_num, by norm_num⟩
      · -- n = 16
        refine ⟨1, by norm_num, by norm_num, by norm_num⟩
      · -- n = 19
        refine ⟨2, by norm_num, by norm_num, by norm_num⟩
      · -- n = 22
        refine ⟨3, by norm_num, by norm_num, by norm_num⟩
      · -- n = 25
        refine ⟨4, by norm_num, by norm_num, by norm_num⟩
      · -- n = 28
        refine ⟨5, by norm_num, by norm_num, by norm_num⟩
      · -- n = 31
        refine ⟨6, by norm_num, by norm_num, by norm_num⟩
      · -- n = 34
        refine ⟨7, by norm_num, by norm_num, by norm_num⟩
      · -- n = 37
        refine ⟨8, by norm_num, by norm_num, by norm_num⟩
      · -- n = 40
        refine ⟨9, by norm_num, by norm_num, by norm_num⟩
      · -- n = 43
        refine ⟨10, by norm_num, by norm_num, by norm_num⟩
      · -- n = 46
        refine ⟨11, by norm_num, by norm_num, by norm_num⟩
      · -- n = 49
        refine ⟨12, by norm_num, by norm_num, by norm_num⟩
      · -- n = 52
        refine ⟨13, by norm_num, by norm_num, by norm_num⟩
      · -- n = 55
        refine ⟨14, by norm_num, by norm_num, by norm_num⟩
      · -- n = 58
        refine ⟨15, by norm_num, by norm_num, by norm_num⟩
      · -- n = 61
        refine ⟨16, by norm_num, by norm_num, by norm_num⟩
      · -- n = 64
        refine ⟨17, by norm_num, by norm_num, by norm_num⟩
      · -- n = 67
        refine ⟨18, by norm_num, by norm_num, by norm_num⟩
      · -- n = 70
        refine ⟨19, by norm_num, by norm_num, by norm_num⟩
      · -- n = 73
        refine ⟨20, by norm_num, by norm_num, by norm_num⟩
  rw [h]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }