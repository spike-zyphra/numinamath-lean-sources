import Mathlib

theorem number_theory_232517 (n : ℕ) (h₀ : n < 20) (h₁ : n + 1 < 20) (h₂ : n + 2 < 20)
    (h₃ : Nat.Prime n) (h₄ : Even (n + 1)) (h₅ : ∃ k, n + 2 = k * (k + 1) / 2) :
    n * (n + 1) * (n + 2) = 2730 := by 
  have h6 : n ≤ 17 := by linarith 
  interval_cases n <;> norm_num at h₃ h₄ h₅ ⊢ 
  <;> try { 
    rcases h₅ with ⟨k, hk⟩ 
    have h7 : k ≤ 19 := by 
      by_contra h 
      push_neg at h 
      have h8 : k * (k + 1) / 2 ≥ 190 := by
        have h9 : k ≥ 19 := by linarith
        have h10 : k + 1 ≥ 19 + 1 := by linarith
        have h11 : k * (k + 1) ≥ 19 * (19 + 1) := by
          nlinarith 
        have h12 : k * (k + 1) / 2 ≥ 19 * (19 + 1) / 2 := by
          apply Nat.div_le_div 
          all_goals linarith 
        norm_num at h12 ⊢ 
        all_goals linarith 
      omega 
    interval_cases k <;> omega 
  }