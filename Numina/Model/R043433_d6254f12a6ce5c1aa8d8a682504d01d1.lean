import Mathlib

theorem number_theory_16499 :
    Set.ncard {n : ℤ | n ∈ Finset.Ico 1 100 ∧ ∃k > 0, n = k^2 ∧ ∃m > 0, n = m^3} = 2 := by 
  have h1 : {n : ℤ | n ∈ Finset.Ico 1 100 ∧ ∃k > 0, n = k^2 ∧ ∃m > 0, n = m^3} = {1, 64} := by
    ext n
    simp only [Finset.mem_Ico, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First, prove the forward direction: if n is in the set, then n ∈ {1, 64}
      rintro ⟨⟨hn1, hn2⟩, ⟨k, hk1, hneqk, m, hm1, hneqm⟩⟩
      have h2 : k ≤ 9 := by nlinarith
      have h3 : m ≤ 4 := by
        by_contra h
        push_neg at h
        have h4 : m ≥ 5 := by omega
        have h5 : (m : ℤ) ^ 3 ≥ 125 := by
          have hm5 : m ≥ 5 := by linarith
          have : (m : ℤ) ^ 3 ≥ (5 : ℤ) ^ 3 := by
            apply pow_le_pow_left
            all_goals linarith
          nlinarith
        nlinarith
      interval_cases k <;> interval_cases m <;> omega
    · -- Now prove the reverse: if n ∈ {1, 64}, then n is in the set
      rintro (rfl | rfl)
      · -- Case 1: n = 1
        constructor
        · -- Show 1 ∈ [1, 100)
          exact ⟨by norm_num, by norm_num⟩
        · -- Show ∃k > 0, 1 = k^2 ∧ ∃m > 0, 1 = m^3
          refine ⟨1, by norm_num, by norm_num, 1, by norm_num, by norm_num⟩
      · -- Case 2: n = 64
        constructor
        · -- Show 64 ∈ [1, 100)
          exact ⟨by norm_num, by norm_num⟩
        · -- Show ∃k > 0, 64 = k^2 ∧ ∃m > 0, 64 = m^3
          refine ⟨8, by norm_num, by norm_num, 4, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.ncard_pair (by norm_num)]