import Mathlib

theorem number_theory_119025 :
    {n : ℕ | n ∈ Finset.Icc 10 99 ∧ ∃ k, n % 36 = k ^ 2} =
    {16, 25, 36, 37, 40, 45, 52, 61, 72, 73, 76, 81, 88, 97} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First direction: if n ∈ {n | n ∈ [10, 99] ∧ ∃ k, n % 36 = k ^ 2}, then n ∈ { explicit set }
    rintro ⟨⟨hn1, hn2⟩, ⟨k, hkn⟩⟩
    have hk1 : k ≤ 5 := by
      by_contra h
      push_neg at h
      have hk2 : k ^ 2 ≥ 36 := by
        have h1 : k ≥ 6 := by omega
        have h2 : k ^ 2 ≥ 36 := by
          nlinarith [h1]
        linarith
      have h1 : n % 36 < 36 := by
        omega
      omega
    interval_cases k <;> omega
  · -- Second direction: if n ∈ { explicit set }, then n ∈ {n | n ∈ [10, 99] ∧ ∃ k, n % 36 = k ^ 2}
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- n = 16
      constructor
      · norm_num
      · use 4
        all_goals norm_num
    · -- n = 25
      constructor
      · norm_num
      · use 5
        all_goals norm_num
    · -- n = 36
      constructor
      · norm_num
      · use 0
        all_goals norm_num
    · -- n = 37
      constructor
      · norm_num
      · use 1
        all_goals norm_num
    · -- n = 40
      constructor
      · norm_num
      · use 2
        all_goals norm_num
    · -- n = 45
      constructor
      · norm_num
      · use 3
        all_goals norm_num
    · -- n = 52
      constructor
      · norm_num
      · use 4
        all_goals norm_num
    · -- n = 61
      constructor
      · norm_num
      · use 5
        all_goals norm_num
    · -- n = 72
      constructor
      · norm_num
      · use 0
        all_goals norm_num
    · -- n = 73
      constructor
      · norm_num
      · use 1
        all_goals norm_num
    · -- n = 76
      constructor
      · norm_num
      · use 2
        all_goals norm_num
    · -- n = 81
      constructor
      · norm_num
      · use 3
        all_goals norm_num
    · -- n = 88
      constructor
      · norm_num
      · use 4
        all_goals norm_num
    · -- n = 97
      constructor
      · norm_num
      · use 5
        all_goals norm_num