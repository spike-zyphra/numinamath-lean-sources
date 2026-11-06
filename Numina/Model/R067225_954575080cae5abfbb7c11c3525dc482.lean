import Mathlib

theorem number_theory_143124 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : 24 * m = n ^ 4) :
    m ≥ 54 := by 
  by_contra h1
  push_neg at h1
  have h3 : 24 * m < 24 * 54 := by
    omega
  have h4 : n ^ 4 < 1296 := by
    omega
  have h5 : n ≤ 5 := by
    by_contra h6
    push_neg at h6
    have h6 : n ≥ 6 := by linarith
    -- we need n > 5 => n >= 6, and then n^4 >= 6^4 = 1296
    have h7 : n ^ 4 ≥ 1296 := by
      have h8 : n ≥ 6 := h6
      have h9 : n ^ 4 ≥ 6 ^ 4 := by
        have h10 : n ≥ 6 := h8
        have : n^4 ≥ 6^4 := by 
          apply Nat.pow_le_pow_of_le_left
          exact h10
          all_goals nlinarith
        linarith 
      norm_num at h9 ⊢
      linarith
    linarith
  -- since n <= 5, and n > 0, n could be 1, 2, 3, 4, 5.  We handle all cases.
  interval_cases n <;> omega