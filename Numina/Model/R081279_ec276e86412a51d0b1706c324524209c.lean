import Mathlib

theorem algebra_233399 (n : ℕ) (h : ∑ i in Finset.range 4, (i + 1)^3 = 10^n) :
    n = 2 := by
  norm_num [Finset.sum_range_succ] at h
  have h1 : (10 : ℕ) ^ n = 100 := by 
    omega
  have h2 : n = 2 := by
    have h4 : (10 : ℕ) ^ n = 100 := h1
    have h5 : n ≤ 3 := by
      by_contra h6
      push_neg at h6
      have h6 : n ≥ 4 := by omega
      have h7 : (10 : ℕ) ^ n ≥ (10 : ℕ) ^ 4 := by
        have h8 : n ≥ 4 := h6
        exact Nat.pow_le_pow_of_le_right (by norm_num) h8
      norm_num at h7
      linarith [h4, h7]
      all_goals omega
    interval_cases n <;> norm_num at h4 <;> omega
  exact h2