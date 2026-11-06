import Mathlib

theorem algebra_153495 (x : ℕ) (h : 7^(2*x) - 48 * 7^x = 49) : x = 2 := by 
  have h1 : 7 ^ (2 * x) = (7 ^ x) ^ 2 := by 
    ring_nf 
  rw [h1] at h 
  have h2 : (7 ^ x : ℕ) ≤ 49 := by 
    by_contra h3 
    push_neg at h3 
    have h4 : (7 ^ x : ℕ) ≥ 50 := by 
      omega 
    -- Now we need to derive `False` from h and h4
    have h5 : (7 ^ x : ℕ) ^ 2 = 48 * (7 ^ x : ℕ) + 49 := by 
      omega 
    have h6 : (7 ^ x : ℕ) ≤ 24 := by 
      nlinarith [h5, sq_nonneg ((7 ^ x : ℕ) : ℤ)]
    nlinarith 
  have h3 : (7 ^ x : ℕ) ≤ 49 := h2 
  have h4 : x ≤ 2 := by 
    by_contra h4 
    push_neg at h4 
    have h5 : x ≥ 3 := by 
      omega 
    have h6 : (7 ^ x : ℕ) ≥ 343 := by 
      have h7 : x ≥ 3 := h5 
      have h8 : 7 ^ x ≥ 7 ^ 3 := by 
        apply Nat.pow_le_pow_of_le_right 
        all_goals norm_num 
        all_goals omega 
      have h9 : 7 ^ 3 = 343 := by 
        norm_num 
      nlinarith [h9] 
    nlinarith 
  have h5 : x = 0 ∨ x = 1 ∨ x = 2 := by 
    omega 
  rcases h5 with (h5 | h5 | h5)
  · -- x = 0 
    rw [show x = 0 by omega] at h 
    all_goals 
      norm_num at h 
  · -- x = 1 
    rw [show x = 1 by omega] at h 
    all_goals 
      norm_num at h 
  · -- x = 2 
    exact_mod_cast h5