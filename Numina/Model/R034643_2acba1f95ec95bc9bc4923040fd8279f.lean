import Mathlib

theorem number_theory_6199 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : 1^4 + 5^4 + 6^4 + a^4 + b^4 = 2019) :
    a + b = 5 := by 
  have h_eq1 : a ^ 4 + b ^ 4 = 97 := by 
    omega 
  have h_eq3 : a ≤ 5 := by
    have h2 : a ^ 4 ≤ 97 := by 
      omega 
    by_contra h3 
    push_neg at h3
    have h4 : a ≥ 6 := by omega 
    have h5 : a ^ 4 ≥ 6 ^ 4 := by 
      have h6 : a ≥ 6 := h4 
      have : a ^ 4 ≥ 6 ^ 4 := by 
        apply Nat.pow_le_pow_of_le_left 
        all_goals linarith 
      linarith 
    have h6 : a^4 ≥ 1296 := by 
      norm_num at h5 ⊢ 
      linarith 
    omega
  have h_eq4 : b ≤ 5 := by 
    have h3 : b ^ 4 ≤ 97 := by 
      omega 
    by_contra h4 
    push_neg at h4 
    have h5 : b ≥ 6 := by omega 
    have h6 : b ^ 4 ≥ 6 ^ 4 := by 
      have h7 : b ≥ 6 := h5 
      have : b ^ 4 ≥ 6 ^ 4 := by 
        apply Nat.pow_le_pow_of_le_left 
        all_goals linarith 
      linarith 
    have h6' : b^4 ≥ 1296 := by 
      norm_num at h6 ⊢ 
      linarith 
    omega 
  interval_cases a <;> interval_cases b 
  <;> omega