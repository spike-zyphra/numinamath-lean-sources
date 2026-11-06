import Mathlib

theorem number_theory_147073 (n : ℕ) (h : n > 0) :
    (512 : ℕ) = 2 ^ n ↔ n = 9 := by
  constructor
  · -- Proof of the forward direction: if 512 = 2^n, then n = 9
    intro h_eq
    have h1 : 2 ^ n = 512 := by 
      omega
    have h2 : n ≤ 9 := by
      by_contra h'
      push_neg at h'
      have h3 : n ≥ 10 := by 
        omega
      have h4 : 2 ^ n ≥ 2 ^ 10 := by 
        apply Nat.pow_le_pow_of_le_right (by norm_num) h3
      norm_num at h1 h4
      all_goals linarith
    have h3 : n ≥ 9 := by
      by_contra h'
      push_neg at h'
      have h3 : n ≤ 8 := by 
        omega
      have h4 : 2 ^ n ≤ 2 ^ 8 := by 
        apply Nat.pow_le_pow_of_le_right (by norm_num) h3
      norm_num at h1 h4
      all_goals linarith
    have : n = 9 := by
      linarith
    exact this
  · -- Proof of the reverse direction: if n = 9, then 512 = 2^n
    intro h_eq
    rw [h_eq]
    all_goals
      norm_num