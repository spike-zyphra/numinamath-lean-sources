import Mathlib

theorem number_theory_225 {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : c / a = (10 ^ b - 1) / (10 ^ b + 1)) :
    c / a = 2 / 5 ∨ c / a = 4 / 8 ∨ c / a = 1 / 4 ∨ c / a = 1 / 5 := by
  have h1 : (10 ^ b - 1) / (10 ^ b + 1) = 0 := by 
    have h5 : 10 ^ b ≥ 10 := by 
      have : b ≥ 1 := by 
        by_contra h'
        push_neg at h'
        have : b = 0 := by linarith 
        contradiction 
      have h7 : 10 ^ b ≥ 10 ^ 1 := by
        apply Nat.pow_le_pow_of_le_right 
        all_goals omega 
      have h77 : 10 ^ 1 = 10 := by norm_num 
      omega 
    have h14 : 10 ^ b - 1 < 10 ^ b + 1 := by 
      omega 
    have h14' : ((10 ^ b + 1) > 0) := by omega 
    simp [Nat.div_eq_zero_iff, h14]
  rw [h1] at h 
  have h4c : c / a = 0 := h
  have h6c : c < a := by
    by_contra h'
    push_neg at h'
    -- c >= a
    have h10 : c / a > 0 := by
      apply Nat.div_pos
      all_goals omega
    omega
  -- Let's check the range.
  all_goals 
    omega