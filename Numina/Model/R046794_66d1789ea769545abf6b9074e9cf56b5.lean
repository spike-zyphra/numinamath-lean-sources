import Mathlib
theorem number_theory_180117 (f : ℤ → ℤ) (h₀ : ∀ x, f (-x) = f x) (h₁ : f 1 = 1)
    (h₂ : f 2008 ≠ 1) (h₃ : ∀ a b, f (a + b) ≤ max (f a) (f b)) :
    f 2009 = 1 := by 
  have h4 : f 0 ≤ 1 := by 
    have h7 := h₃ 1 (-1)
    norm_num at h7 
    have h8 : f (-1) = f 1 := h₀ 1 
    rw [h8, h₁] at h7 
    omega 
  have h5 : ∀ n : ℕ, f n ≤ 1 := by 
    intro n 
    induction n with 
    | zero => 
      exact h4 
    | succ n ih => 
      have h9 := h₃ n 1 
      norm_num at h9 ⊢ 
      cases' max_cases (f n) (f 1) with h6 h6 
      · 
        omega 
      · 
        omega 
  have h6 : f 2009 ≤ 1 := by 
    specialize h5 2009 
    norm_num at h5 ⊢ 
    all_goals linarith
  have h8 : f 2008 ≤ 1 := by 
    specialize h5 2008 
    norm_num at h5 ⊢ 
    all_goals linarith 
  have h7 : 1 ≤ f 2009 := by
    have h8_1 := h₃ 2009 (-2008) 
    norm_num at h8_1 ⊢ 
    have h9 : f (-2008) = f 2008 := h₀ 2008 
    rw [h9] at h8_1 
    by_cases h9 : f 2008 < 1 
    · 
      have h11 : f 2008 < 1 := h9 
      have h10 : f 2008 ≤ 0 := by omega 
      cases max_cases (f 2009) (f 2008) with 
      | inl h14 => 
        omega 
      | inr h15 => 
        omega 
    · 
      have h11 : f 2008 ≥ 1 := by omega 
      have h12 : f 2008 = 1 := by 
        omega 
      have h13 : f 2008 = 1 := h12 
      have h14 : f 2008 = 1 := h12 
      have h15 : f 2008 ≠ 1 := h₂ 
      contradiction 
  linarith [h7, h6]