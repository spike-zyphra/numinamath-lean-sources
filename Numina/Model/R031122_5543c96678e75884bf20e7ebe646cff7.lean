import Mathlib

theorem number_theory_171796 : {n : ℕ | n ∈ Finset.Icc 1 100 ∧ ∃ k, k^2 = 8 * n + 1}.ncard = 13 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 100 ∧ ∃ k, k^2 = 8 * n + 1} = 
    {1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91} := by 
    ext n 
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
      Set.mem_singleton_iff, and_imp]
    constructor 
    · -- First, prove {n : ℕ | n ∈ Finset.Icc 1 100 ∧ ∃ k, k^2 = 8 * n + 1}
      rintro ⟨⟨hn1, hn2⟩, ⟨k, hkn⟩⟩ 
      have h2 : k ≤ 28 := by
        by_contra h 
        push_neg at h 
        have h3 : k ^ 2 > 800 := by
          have : k ≥ 29 := by linarith
          nlinarith 
        nlinarith 
      interval_cases k <;> omega 
    · -- Show that if n ∈ {1,3,6, 10, ..., 91}, then n ∈ { ... }
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show {n=1}
        constructor
        · norm_num 
        · use 3 
          all_goals norm_num 
      · -- n=3
        constructor 
        · norm_num 
        · use 5
          all_goals norm_num 
      · -- n=6
        constructor 
        · norm_num 
        · use 7
          all_goals norm_num 
      · -- n=10
        constructor 
        · norm_num 
        · use 9
          all_goals norm_num 
      · -- n=15
        constructor 
        · norm_num 
        · use 11
          all_goals norm_num 
      · -- n=21
        constructor 
        · norm_num 
        · use 13
          all_goals norm_num 
      · -- n=28
        constructor 
        · norm_num 
        · use 15
          all_goals norm_num 
      · -- n=36
        constructor 
        · norm_num 
        · use 17
          all_goals norm_num 
      · -- n=45
        constructor 
        · norm_num 
        · use 19
          all_goals norm_num 
      · -- n=55
        constructor 
        · norm_num 
        · use 21
          all_goals norm_num 
      · -- n=66
        constructor 
        · norm_num 
        · use 23
          all_goals norm_num 
      · -- n=78
        constructor 
        · norm_num 
        · use 25
          all_goals norm_num 
      · -- n=91
        constructor 
        · norm_num 
        · use 27
          all_goals norm_num 
  rw [h1] 
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
  <;> try { native_decide }