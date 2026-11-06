import Mathlib

theorem algebra_193689 {g b : ℕ} (h₀ : g + b = 108) (h₁ : g ∣ 480 / 2) (h₂ : b ∣ 480 / 2) (h₃ : 480 / 2 / g = 480 / 2 / b + 1) : g = 48 ∧ b = 60 := by
  have h4 : 480 / 2 = 240 := by norm_num
  have h₄ : 240 / g = 240 / b + 1 := by
    rw [show 480 / 2 = 240 by norm_num] at h₃
    omega

  have h5 : b = 108 - g := by
    omega

  have h6 : g ≤ 240 := by
    have h7 : g ∣ 240 := by
      have h8 : g ∣ 480 / 2 := h₁
      rw [show 480 / 2 = 240 by norm_num] at h8
      exact h8
    have h8 : g ∣ 240 := h7
    have h9 : g ≤ 240 := by
      exact Nat.le_of_dvd (by norm_num) h8
    omega
  have h7 : b ≤ 240 := by
    have h8 : b ∣ 240 := by
      have h9 : b ∣ 480 / 2 := h₂
      rw [show 480 / 2 = 240 by norm_num] at h9
      exact h9
    have h9 : b ∣ 240 := h8
    have h10 : b ≤ 240 := by
      exact Nat.le_of_dvd (by norm_num) h9
    omega
  
  have h8 : g ≥ 1 := by
    by_contra h
    push_neg at h
    have h9 : g = 0 := by
      omega
    have h10 : b = 108 := by
      omega
    rw [h9, h10] at h₄
    norm_num at h₄

  have h9 : b ≥ 1 := by 
    by_contra h 
    push_neg at h 
    have h10 : b = 0 := by
      omega
    have h11 : g = 108 := by
      omega 
    rw [h11, h10] at h₄
    norm_num at h₄
  
  have h10 : g ≤ 108 := by 
    omega 

  interval_cases g <;> norm_num [h5] at h₄ h₁ h₂ ⊢ 
  all_goals 
    try { 
      omega 
    }