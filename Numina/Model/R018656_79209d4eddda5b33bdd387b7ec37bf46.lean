import Mathlib


theorem number_theory_175510 :
    Set.ncard {n : ℕ | 10 ≤ n ∧ n < 100 ∧ ∃ k, k^2 = (Nat.digits 10 n).sum} = 17 := by 
  have : {n : ℕ | 10 ≤ n ∧ n < 100 ∧ ∃ k, k^2 = (Nat.digits 10 n).sum} = 
    {10, 13, 22, 31, 40, 18, 27, 36, 45, 54, 63, 72, 81, 90, 79, 88, 97} := by
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert,  Set.union_singleton]
    constructor
    · -- Assume n in {n : ℕ | 10 ≤ n ∧ n < 100 ∧ ∃ k, k^2 = (Nat.digits 10 n).sum}, prove n in {10,13, ... ,97}
      rintro ⟨h10, h100, ⟨k, hk⟩⟩
      have h3 : k ≤ 4 := by
        by_contra h
        push_neg at h
        have hk5 : k ≥ 5 := by omega
        have hk2 : k^2 ≥ 25 := by 
          have : k ≥ 5 := by linarith 
          nlinarith [sq_nonneg (k - 5)]
        have hk4 : k^2 ≤ 18 := by 
          interval_cases n <;> norm_num at hk ⊢ 
          all_goals 
            omega
        nlinarith
      interval_cases k <;> try { 
        norm_num at hk 
        all_goals 
          interval_cases n <;> norm_num at hk ⊢ 
          <;> 
            omega 
      }
    · -- Assume n in {10,13, ... ,97}, prove n in {n : ℕ | 10 ≤ n ∧ n < 100 ∧ ∃ k, k^2 = (Nat.digits 10 n).sum}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 10
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 1
          all_goals norm_num 
      · -- n = 13
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 2
          all_goals norm_num 
      · -- n = 22
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 2
          all_goals norm_num 
      · -- n = 31
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 2
          all_goals norm_num 
      · -- n = 40
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 2
          all_goals norm_num 
      · -- n = 18
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 3
          all_goals norm_num 
      · -- n = 27
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 3
          all_goals norm_num 
      · -- n = 36
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 3
          all_goals norm_num 
      · -- n = 45
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 3
          all_goals norm_num 
      · -- n = 54
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 3
          all_goals norm_num 
      · -- n = 63
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 3
          all_goals norm_num 
      · -- n = 72
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 3
          all_goals norm_num 
      · -- n = 81
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 3
          all_goals norm_num 
      · -- n = 90
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 3
          all_goals norm_num 
      · -- n = 79
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 4
          all_goals norm_num 
      · -- n = 88
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 4
          all_goals norm_num 
      · -- n = 97
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 4
          all_goals norm_num 
  rw [this]
  rw [Set.ncard_eq_toFinset_card']
  simp