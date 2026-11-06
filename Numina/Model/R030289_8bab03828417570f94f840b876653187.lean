import Mathlib

theorem number_theory_6320 :
    Set.ncard {n : ℕ | 0 < n ∧ ∃ k, n = k^2 ∧ 9 ∣ n ∧ n < 2021} = 14 := by
  have h1 : {n : ℕ | 0 < n ∧ ∃ k, n = k^2 ∧ 9 ∣ n ∧ n < 2021} = 
      {9, 36, 81, 144, 225, 324, 441, 576, 729, 900, 1089, 1296, 1521, 1764} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: the set is contained in the 14 elements.
      rintro ⟨hn_pos, ⟨k, rfl, hk1, hk2⟩⟩
      have hk3 : k ≤ 44 := by
        by_contra h
        push_neg at h
        have h2 : k ^ 2 ≥ 2025 := by
          have : k ≥ 45 := by linarith
          calc
            k ^ 2 ≥ 45 ^ 2 := by apply Nat.pow_le_pow_left; exact this
            _ = 2025 := by norm_num
        linarith
      interval_cases k <;> norm_num at *
    · -- Second direction: each of the 14 elements is in the set.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 9
        refine ⟨by norm_num, ⟨3, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 36
        refine ⟨by norm_num, ⟨6, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 81
        refine ⟨by norm_num, ⟨9, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 144
        refine ⟨by norm_num, ⟨12, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 225
        refine ⟨by norm_num, ⟨15, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 324
        refine ⟨by norm_num, ⟨18, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 441
        refine ⟨by norm_num, ⟨21, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 576
        refine ⟨by norm_num, ⟨24, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 729
        refine ⟨by norm_num, ⟨27, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 900
        refine ⟨by norm_num, ⟨30, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 1089
        refine ⟨by norm_num, ⟨33, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 1296
        refine ⟨by norm_num, ⟨36, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 1521
        refine ⟨by norm_num, ⟨39, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 1764
        refine ⟨by norm_num, ⟨42, by norm_num, by norm_num, by norm_num⟩⟩
  rw [h1]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_insert_of_not_mem]
  rw [Set.ncard_singleton]
  all_goals norm_num [Nat.pow_mod]