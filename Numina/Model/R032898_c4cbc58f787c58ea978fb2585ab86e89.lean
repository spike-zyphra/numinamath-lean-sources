import Mathlib

theorem number_theory_261093 :
  {n : ℕ | n > 0 ∧ (n * (n + 1)) / 2 ∈ Finset.Icc 100 999 ∧ 
   ∃ k, 1 ≤ k ∧ k ≤ 9 ∧ (n * (n + 1)) / 2 = k * 111} = {36} := by
  ext n 
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor 
  · -- Assume h, prove n = 36 
    intro h 
    rcases h with ⟨hn_pos, ⟨hn1, hn2⟩, ⟨k, h_k_ge, h_k_le, h_eq⟩⟩ 
    have h2 : n * (n + 1) / 2 = k * 111 := h_eq
    have h3 : n * (n + 1) / 2 ≥ 100 := by 
      omega 
    have h4 : n * (n + 1) / 2 ≤ 999 := by 
      omega 
    have : k ≤ 9 := h_k_le
    have : k ≥ 1 := h_k_ge
    interval_cases k <;> 
      try { 
        norm_num at h2 
        have h5 : n ≤ 44 := by 
          by_contra h 
          push_neg at h 
          have h6 : n * (n + 1) / 2 > 999 := by 
            have : n ≥ 45 := by omega 
            have : n * (n + 1) ≥ 45 * 46 := by 
              nlinarith 
            omega 
          omega 
        have h6 : n ≥ 14 := by 
          by_contra h 
          push_neg at h 
          have h7 : n * (n + 1) / 2 < 100 := by 
            have : n ≤ 13 := by omega 
            interval_cases n <;> omega 
          omega 
        interval_cases n <;> omega 
      }
  · -- Assume n = 36, prove all 
    intro h_eq 
    rw [h_eq] 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    · -- There exists k such that (36 * 37) / 2 = k * 111 
      use 6 
      all_goals norm_num