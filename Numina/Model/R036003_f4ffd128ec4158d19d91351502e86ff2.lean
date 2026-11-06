import Mathlib

theorem algebra_21713 {f : ℕ → ℕ} (hf0 : f 0 = 1) (hf1 : f 1 = 1) (hf2 : ∀n, f n > 0)
    (hfm : ∀ n m, n ≥ m + 1 → 
      (f n * f (m + 1)) / f m + (f n * f (n - m)) / f (n - m - 1) = f (n + 1)
    ) : IsLeast {n | f n > 10 ^ 6} 10 := by
  have h2 : f 0 = 1 := hf0
  have h3 : f 1 = 1 := hf1
  have h4 : f 2 = 2 := by 
    specialize hfm 1 0 (by norm_num)
    simp [h2, h3] at hfm
    omega
  have h5 : f 3 = 6 := by 
    specialize hfm 2 1 (by norm_num)
    norm_num [h4, h3, h2] at hfm ⊢
    all_goals 
      omega
  have h6 : f 4 = 24 := by 
    specialize hfm 3 2 (by norm_num)
    norm_num [h5, h4, h3, h2] at hfm ⊢
    all_goals 
      omega
  have h7 : f 5 = 120 := by 
    specialize hfm 4 3 (by norm_num)
    norm_num [h6, h5, h4, h3, h2] at hfm ⊢
    all_goals 
      omega
  have h8 : f 6 = 720 := by 
    specialize hfm 5 4 (by norm_num)
    norm_num [h7, h6, h5, h4, h3, h2] at hfm ⊢
    all_goals 
      omega
  have h9 : f 7 = 5040 := by 
    specialize hfm 6 5 (by norm_num)
    norm_num [h8, h7, h6, h5, h4, h3, h2] at hfm ⊢
    all_goals 
      omega
  have h10 : f 8 = 40320 := by 
    specialize hfm 7 6 (by norm_num)
    norm_num [h9, h8, h7, h6, h5, h4, h3, h2] at hfm ⊢
    all_goals 
      omega
  have h11 : f 9 = 362880 := by 
    specialize hfm 8 7 (by norm_num)
    norm_num [h10, h9, h8, h7, h6, h5, h4, h3, h2] at hfm ⊢
    all_goals 
      omega
  have h12 : f 10 = 3628800 := by 
    specialize hfm 9 8 (by norm_num)
    norm_num [h11, h10, h9, h8, h7, h6, h5, h4, h3, h2] at hfm ⊢
    all_goals 
      omega
  constructor
  · -- Show that 10 is in the set 
    rw [Set.mem_setOf_eq]
    norm_num [h12]
  · -- Show that no smaller n is in the set 
    intro n hn
    rw [Set.mem_setOf_eq] at hn
    by_contra h 
    push_neg at h 
    interval_cases n <;> norm_num [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] at hn ⊢
    all_goals omega