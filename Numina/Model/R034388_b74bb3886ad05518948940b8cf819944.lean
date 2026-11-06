import Mathlib

theorem number_theory_251327 (n m : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : m ∈ Finset.Icc 100 999)
    (h₂ : (Nat.digits 10 n).length = 3) (h₃ : (Nat.digits 10 m).length = 3)
    (h₄ : (Nat.digits 10 n).toFinset.card = 3) (h₅ : (Nat.digits 10 m).toFinset.card = 3)
    (h₆ : (Nat.digits 10 n).toFinset ∩ (Nat.digits 10 m).toFinset = ∅)
    (h₇ : n + m = 1000) :
    min n m ≤ 498 := by
  rw [Finset.mem_Icc] at h₀ h₁
  rcases h₀ with ⟨h₈, h₉⟩
  rcases h₁ with ⟨h₁₀, h₁₁⟩
  by_contra h 
  push_neg at h 
  have h8 : min n m > 498 := h 
  have h9 : n > 498 := by
    have h9 : n ≥ min n m := by 
      cases min_cases n m with 
      | inl h => 
        omega 
      | inr h => 
        omega 
    omega 
  have h10 : m > 498 := by 
    have h10 : m ≥ min n m := by 
      cases min_cases n m with 
      | inl h => 
        omega 
      | inr h => 
        omega 
    omega 
  have hn1 : n ≤ 501 := by 
    omega
  have hn2 : n ≥ 499 := by 
    omega 
  have hm1 : m = 1000 - n := by 
    omega 
  interval_cases n <;> norm_num [hm1] at h₇ h₃ h₄ h₅ h₆ h₈ h₉ h₁₀ h₁₁ h9 h10 ⊢ <;> 
    try { 
      all_goals 
      contradiction 
    } <;> try { 
      all_goals 
      tauto 
    }