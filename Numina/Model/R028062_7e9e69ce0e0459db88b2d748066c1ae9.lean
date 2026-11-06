import Mathlib

theorem number_theory_235717 :
    IsLeast {n | ∀ k ∈ Finset.Ico 1 10, (2013000 + n) % k = 0} 480 := by
  constructor
  · -- Show that 480 is in the set
    intro k hk
    have h1 : k ∈ Finset.Ico 1 10 := hk
    have h2 : k > 0 := by 
      simp [Finset.mem_Ico] at h1 ⊢
      omega 
    have h3 : k < 10 := by 
      simp [Finset.mem_Ico] at h1 ⊢
      omega 
    interval_cases k <;> norm_num 
  · -- Show 480 is the smallest
    intro n hn
    have h1 : ∀ k ∈ Finset.Ico 1 10, (2013000 + n) % k = 0 := hn 
    have h2 := h1 7 (by simp [Finset.mem_Ico])
    have h3 := h1 8 (by simp [Finset.mem_Ico])
    have h4 := h1 5 (by simp [Finset.mem_Ico])
    have h5 := h1 9 (by simp [Finset.mem_Ico])
    norm_num at h2 h3 h4 h5 
    omega