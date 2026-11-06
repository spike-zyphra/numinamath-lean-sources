import Mathlib

def star (a b : ℕ) := a ^ b + a * b

theorem algebra_11891 {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (h : star a b = 15) :
    a + b = 5 := by 
  have h1 : a ^ b + a * b = 15 := by 
    have h1' : star a b = a ^ b + a * b := by rfl 
    rw [h1'] at h 
    linarith 
  have h2 : a ≤ 3 := by 
    by_contra h3
    push_neg at h3
    have h3' : a ≥ 4 := by omega
    have h4 : b ≥ 2 := by linarith
    have h5 : a ^ b ≥ a ^ 2 := by
      apply Nat.pow_le_pow_of_le_right 
      all_goals 
        omega 
    have h6 : a ^ 2 ≥ 16 := by 
      nlinarith [sq_nonneg (a : ℕ)]
    have h7 : a * b ≥ 8 := by 
      nlinarith [show b ≥ 2 by linarith] 
    have h8 : a ^ b + a * b ≥ 24 := by 
      have h9 : a ^ b ≥ 16 := by 
        linarith 
      nlinarith 
    linarith
  have h3 : b ≤ 3 := by 
    by_contra h4 
    push_neg at h4 
    have h4' : b ≥ 4 := by omega 
    have h5 : a ≥ 2 := by linarith 
    have h6 : a ^ b ≥ a ^ 4 := by 
      apply Nat.pow_le_pow_of_le_right 
      all_goals 
        omega 
    have h7 : a ^ 4 ≥ 16 := by 
      have h8 : a ≥ 2 := by linarith 
      have h9 : a ^ 4 ≥ 16 := by
        have h10 : a ≥ 2 := h8 
        have h11 : a ^ 4 ≥ 2 ^ 4 := by 
          apply Nat.pow_le_pow_of_le_left 
          all_goals 
            omega 
        norm_num at h11 ⊢ 
        linarith 
      linarith 
    have h10 : a * b ≥ 8 := by 
      nlinarith [show b ≥ 4 by linarith, show a ≥ 2 by linarith] 
    have h11 : a ^ b + a * b ≥ 24 := by 
      have h9 : a ^ b ≥ 16 := by 
        linarith 
      nlinarith 
    linarith 
  have h4 : a ≤ 3 := h2
  have h5 : b ≤ 3 := h3
  interval_cases a <;> interval_cases b
  all_goals 
    norm_num at h1 ⊢
    all_goals omega