import Mathlib

theorem number_theory_176911 (a : ℕ → ℕ)
    (h₀ : ∀ n, a n = if n < 6 then n + 1 else (a (n - 6) + ∑ i ∈ Finset.range 6, (a (n + i)))) :
    ∑ i ∈ Finset.range 99, a i = 5050 ∧ a 99 = 50 := by
  have h1 : a 6 = a 0 + a 6 + a 7 + a 8 + a 9 + a 10 + a 11 := by 
    have h6 : a 6 = a (6 - 6) + ∑ i in Finset.range 6, (a (6 + i)) := by
      specialize h₀ 6 
      norm_num at h₀ ⊢ 
      all_goals try { tauto }
    have h7 : (6 - 6 : ℕ) = 0 := by omega 
    rw [h7] at h6 
    have h8 : (∑ i in Finset.range 6, (a (6 + i)) ) = a 6 + a 7 + a 8 + a 9 + a 10 + a 11 := by 
      simp [Finset.sum_range_succ]
    rw [h8] at h6 
    linarith
  -- Show a 0 = 1
  have h2 : a 0 = 1 := by 
    have h00 : a 0 = if 0 < 6 then 0 + 1 else (a (0 - 6) + ∑ i in Finset.range 6, (a (0 + i))) := h₀ 0 
    norm_num at h00 ⊢ 
    all_goals try { tauto }
  -- Substitute h2 into h1 
  rw [h2] at h1 
  omega