import Mathlib

theorem number_theory_70759 :
    Set.ncard {n : ℕ | ∃ k, (11 * k + 9 * n) = 2007} = 21 := by 
  have h1 : {n : ℕ | ∃ k, (11 * k + 9 * n) = 2007} = {3, 14, 25, 36, 47, 58, 69, 80, 91, 102, 113, 124, 135, 146, 157, 168, 179, 190, 201, 212, 223} := by 
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor 
    · -- First, prove that if exists k s.t. 11k + 9n = 2007, then n must be in the set
      intro h
      rcases h with ⟨k, hk⟩
      have h2 : k ≤ 182 := by
        omega
      have h3 : n ≤ 223 := by
        omega 
      interval_cases n <;> omega 
    · -- Now the reverse implication
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 3
        exact ⟨180, by norm_num⟩
      · -- n = 14
        exact ⟨171, by norm_num⟩
      · -- n = 25
        exact ⟨162, by norm_num⟩
      · -- n = 36
        exact ⟨153, by norm_num⟩
      · -- n = 47
        exact ⟨144, by norm_num⟩
      · -- n = 58
        exact ⟨135, by norm_num⟩
      · -- n = 69
        exact ⟨126, by norm_num⟩
      · -- n = 80
        exact ⟨117, by norm_num⟩
      · -- n = 91
        exact ⟨108, by norm_num⟩
      · -- n = 102
        exact ⟨99, by norm_num⟩
      · -- n = 113
        exact ⟨90, by norm_num⟩
      · -- n = 124
        exact ⟨81, by norm_num⟩
      · -- n = 135
        exact ⟨72, by norm_num⟩
      · -- n = 146
        exact ⟨63, by norm_num⟩
      · -- n = 157
        exact ⟨54, by norm_num⟩
      · -- n = 168
        exact ⟨45, by norm_num⟩
      · -- n = 179
        exact ⟨36, by norm_num⟩
      · -- n = 190
        exact ⟨27, by norm_num⟩
      · -- n = 201
        exact ⟨18, by norm_num⟩
      · -- n = 212
        exact ⟨9, by norm_num⟩
      · -- n = 223
        exact ⟨0, by norm_num⟩
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try native_decide