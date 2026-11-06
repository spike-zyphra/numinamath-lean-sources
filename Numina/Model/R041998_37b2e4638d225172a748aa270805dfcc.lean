import Mathlib

theorem number_theory_95949 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ ∃ k, k^2 = (Nat.digits 10 n).sum} = 17 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ ∃ k, k^2 = (Nat.digits 10 n).sum} = 
    {10, 13, 22, 31, 40, 18, 27, 36, 45, 54, 63, 72, 81, 90, 79, 88, 97} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_Icc]
    constructor
    · -- First part: if n in the given range and digit sum is perfect square, then in the explicit set.
      rintro ⟨⟨h10, h99⟩, ⟨k, hk⟩⟩
      interval_cases n <;> norm_num at hk ⊢ 
      <;> try { 
        all_goals
        have : k ≤ 12 := by nlinarith
        interval_cases k <;> try { tauto }
      }
    · -- Second part: if in the explicit set, then in the range and digit sum is perfect square.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 10
        refine ⟨by norm_num, 1, by norm_num⟩
      · -- n = 13
        refine ⟨by norm_num, 2, by norm_num⟩
      · -- n = 22
        refine ⟨by norm_num, 2, by norm_num⟩
      · -- n = 31
        refine ⟨by norm_num, 2, by norm_num⟩
      · -- n = 40
        refine ⟨by norm_num, 2, by norm_num⟩
      · -- n = 18
        refine ⟨by norm_num, 3, by norm_num⟩
      · -- n = 27
        refine ⟨by norm_num, 3, by norm_num⟩
      · -- n = 36
        refine ⟨by norm_num, 3, by norm_num⟩
      · -- n = 45
        refine ⟨by norm_num, 3, by norm_num⟩
      · -- n = 54
        refine ⟨by norm_num, 3, by norm_num⟩
      · -- n = 63
        refine ⟨by norm_num, 3, by norm_num⟩
      · -- n = 72
        refine ⟨by norm_num, 3, by norm_num⟩
      · -- n = 81
        refine ⟨by norm_num, 3, by norm_num⟩
      · -- n = 90
        refine ⟨by norm_num, 3, by norm_num⟩
      · -- n = 79
        refine ⟨by norm_num, 4, by norm_num⟩
      · -- n = 88
        refine ⟨by norm_num, 4, by norm_num⟩
      · -- n = 97
        refine ⟨by norm_num, 4, by norm_num⟩
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try native_decide