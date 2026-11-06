import Mathlib

theorem number_theory_15452 : IsLeast {N : ℕ | 0 < N ∧ {2, 3, 5, 7} ⊆
    {k : ℕ | ∃ i ∈ Finset.range 3, k ^ 2 ∣ N + i}} 98 := by
  constructor 
  · -- First, we show that 98 belongs to the set 
    constructor 
    · -- Show 0 < 98 
      norm_num 
    · -- Show {2, 3, 5, 7} ⊆ {k : ℕ | ∃ i ∈ Finset.range 3, k ^ 2 ∣ 98 + i}
      intro k hk 
      have hk1 : k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 7 := by 
        simp at hk 
        omega 
      rcases hk1 with (rfl | rfl | rfl | rfl)
      · -- k = 2 
        refine ⟨2, by simp, by norm_num⟩ 
      · -- k = 3 
        refine ⟨1, by simp, by norm_num⟩ 
      · -- k = 5 
        refine ⟨2, by simp, by norm_num⟩ 
      · -- k = 7 
        refine ⟨0, by simp, by norm_num⟩ 
  · -- Now we show that no number less than 98 is in the set
    intro N h 
    rcases h with ⟨hN_pos, hsubset⟩ 
    by_contra h 
    push_neg at h 
    have h2 : (2 : ℕ) ∈ {k : ℕ | ∃ i ∈ Finset.range 3, k ^ 2 ∣ N + i} := hsubset (by simp)
    have h3 : (3 : ℕ) ∈ {k : ℕ | ∃ i ∈ Finset.range 3, k ^ 2 ∣ N + i} := hsubset (by simp)
    have h4 : (5 : ℕ) ∈ {k : ℕ | ∃ i ∈ Finset.range 3, k ^ 2 ∣ N + i} := hsubset (by simp)
    have h5 : (7 : ℕ) ∈ {k : ℕ | ∃ i ∈ Finset.range 3, k ^ 2 ∣ N + i} := hsubset (by simp)
    simp only [Finset.mem_range] at h2 h3 h4 h5 
    rcases h2 with ⟨i2, hi21, h2i⟩ 
    rcases h3 with ⟨i3, hi31, h3i⟩ 
    rcases h4 with ⟨i4, hi41, h4i⟩ 
    rcases h5 with ⟨i5, hi51, h5i⟩ 
    interval_cases i2 <;> interval_cases i3 <;> interval_cases i4 <;> interval_cases i5 
      <;> omega