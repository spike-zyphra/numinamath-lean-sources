import Mathlib

theorem number_theory_894 (m n p : ℤ) (h : |m - n| ^ 3 + |p - m| ^ 5 = 1) :
    |p - m| + |m - n| + 2 * |n - p| = 3 := by
  have h1 : |m - n| ≥ 0 := abs_nonneg (m - n)
  have h2 : |p - m| ≥ 0 := abs_nonneg (p - m)
  have h3 : |m - n| ≤ 1 := by 
    by_contra h4
    push_neg at h4
    have h4' : |m - n| ≥ 2 := by omega
    have h4'' : |m - n| ^ 3 ≥ 8 := by
      have : |m - n| ≥ 2 := h4'
      have h1 : |m - n| ^ 3 ≥ 2 ^ 3 := by apply pow_le_pow_left; all_goals linarith
      norm_num at h1 ⊢
      linarith
    have h5 : |p - m| ^ 5 ≥ 0 := by positivity
    linarith
  have h4 : |p - m| ≤ 1 := by 
    by_contra h5
    push_neg at h5
    have h5' : |p - m| ≥ 2 := by omega
    have h5'' : |p - m| ^ 5 ≥ 32 := by
      have : |p - m| ≥ 2 := h5'
      have h1 : |p - m| ^ 5 ≥ 2 ^ 5 := by apply pow_le_pow_left; all_goals linarith
      norm_num at h1 ⊢
      linarith
    have h6 : |m - n| ^ 3 ≥ 0 := by positivity
    linarith
  have h5 : |m - n| = 0 ∨ |m - n| = 1 := by omega
  have h6 : |p - m| = 0 ∨ |p - m| = 1 := by omega
  rcases h5 with h5 | h5
  · -- |m - n| = 0 
    rcases h6 with h6 | h6
    · -- |p - m| = 0 
      rw [h5, h6] at h 
      norm_num at h
      all_goals 
      omega
    · -- |p - m| = 1 
      rw [h5, h6] at h 
      norm_num at h 
      have hm : m = n := by 
        rw [abs_eq_zero] at h5 
        linarith 
      have h7 : |p - n| = 1 := by 
        have h7 : |p - m| = 1 := by 
          omega 
        rw [show m = n by linarith [hm]] at h7 
        have : |p - n| = 1 := by 
          omega 
        linarith 
      have hpm : |p - m| = 1 := by 
        omega 
      have hmn : |m - n| = 0 := by 
        omega 
      have hnp : |n - p| = 1 := by 
        have hnp : |n - p| = |p - n| := by 
          rw [show n - p = -(p - n) by ring] 
          rw [abs_neg] 
        rw [hnp] 
        linarith [h7] 
      linarith [hpm, hmn, hnp]
  · -- |m - n| = 1 
    rcases h6 with h6 | h6
    · -- |p - m| = 0 
      rw [h5, h6] at h 
      norm_num at h 
      have hp : p = m := by 
        rw [abs_eq_zero] at h6 
        linarith 
      have hmn : |m - n| = 1 := by 
        omega 
      have hp_m : |p - m| = 0 := by 
        rw [hp] 
        norm_num 
      have hn_p : |n - p| = 1 := by 
        rw [show n - p = n - m by rw [hp]] 
        have : |n - m| = |m - n| := by 
          rw [show n - m = -(m - n) by ring] 
          rw [abs_neg] 
        rw [this] 
        omega 
      linarith [hp_m, hmn, hn_p]
    · -- |p - m| = 1 
      rw [h5, h6] at h 
      all_goals 
      norm_num at h 
      all_goals 
      omega