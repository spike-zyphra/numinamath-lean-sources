import Mathlib

theorem number_theory_23417 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 10 ∧ ∃ k > 0, 6 ∣ k ∧ (k - 1) % n = 0 } = 3 := by
  have h1 : {n : ℕ | 0 < n ∧ n < 10 ∧ ∃ k > 0, 6 ∣ k ∧ (k - 1) % n = 0 } = {1, 5, 7} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First, show that if n is in the set, then n must be 1, 5, or 7
      rintro ⟨hn1, hn2, ⟨k, hk1, h1, h2⟩⟩
      interval_cases n <;> try { 
        omega 
      }
      <;> try { 
        have h3 : k ≤ 24 := by 
          omega 
        interval_cases k <;> norm_num at h1 h2 <;> tauto 
      }
      <;> omega 
    · -- Now prove the reverse: if n is in {1,5,7}, then n is in the set 
      rintro (rfl | rfl | rfl)
      · -- Show that n = 1 is in the set
        constructor 
        · norm_num
        constructor 
        · norm_num
        · refine ⟨6, by norm_num, by norm_num, by norm_num⟩ 
      · -- Show that n = 5 is in the set 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · refine ⟨6, by norm_num, by norm_num, by norm_num⟩ 
      · -- Show that n = 7 is in the set 
        constructor 
        · norm_num
        constructor 
        · norm_num
        · refine ⟨36, by norm_num, by norm_num, by norm_num⟩ 
  rw [h1]
  norm_num