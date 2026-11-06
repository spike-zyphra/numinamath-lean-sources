import Mathlib

theorem number_theory_7126
    (p q r : ℕ)
    (h₀ : Nat.Prime p)
    (h₁ : Nat.Prime q)
    (h₂ : Nat.Prime r)
    (h₃ : p * q + p * r = 80)
    (h₄ : p * q + q * r = 425) :
    p + q + r = 42 := by 
  have eq1 : p * (q + r) = 80 := by
    linarith
  have h5 : p = 2 ∨ p = 5 := by
    have h6 : p ∣ 80 := by 
      use q + r
      all_goals linarith
    have h7 : p ≤ 80 := by
      exact Nat.le_of_dvd (by linarith) h6
    interval_cases p <;> norm_num at h₀ h6 eq1 h₃ h₄ <;> omega
  rcases h5 with (hp | hp)
  · -- Assume p = 2
    have h8 : q + r = 40 := by 
      rw [hp] at eq1 
      linarith
    have h9 : q * (2 + r) = 425 := by 
      rw [hp] at h₄
      linarith
    have h10 : q = 5 ∨ q = 17 := by 
      have h11 : q ∣ 425 := by 
        use 2 + r
        all_goals nlinarith
      have h12 : q ≤ 425 := by 
        exact Nat.le_of_dvd (by linarith) h11
      interval_cases q <;> norm_num at h₁ h11 h9 h₃ h₄ <;> omega
    rcases h10 with (hq | hq)
    · -- Assume q = 5
      have h13 : r = 35 := by 
        omega
      rw [h13] at h₂ 
      norm_num at h₂
    · -- Assume q = 17
      have h14 : r = 23 := by 
        omega
      have : p + q + r = 42 := by 
        rw [hp, hq, h14]
        all_goals linarith
      assumption
  · -- Assume p = 5
    -- From eq1: p * (q + r) = 5 * (q + r) = 80 => q + r = 16
    have h8 : q + r = 16 := by 
      rw [hp] at eq1 
      linarith
    -- From h₄: p * q + q * r = 5 * q + q * r = q * (5 + r) = 425
    have h10 : q * (5 + r) = 425 := by 
      rw [hp] at h₄
      linarith
    -- So q divides 425 and q is prime => q = 5 or 17
    have h11 : q = 5 ∨ q = 17 :=  by 
      have h11 : q ∣ 425 := by 
        use 5 + r
        all_goals nlinarith
      have h12 : q ≤ 425 := by 
        exact Nat.le_of_dvd (by linarith) h11
      interval_cases q <;> norm_num at h₁ h11 h10 h₃ h₄ <;> omega
    rcases h11 with (hq | hq)
    · -- Assume q = 5
      -- Then r = 16 - 5 = 11. Then h₄: 5 * 5 + 5 * 11 = 25 + 55 = 80 ≠ 425
      -- Contradicts h₄
      have h13 : r = 11 := by 
          omega 
      rw [hq, h13] at h₄
      all_goals linarith
    · -- Assume q = 17
      -- Then r = 16 - 17 = -1. Negative. Contradicts r is natural
      omega