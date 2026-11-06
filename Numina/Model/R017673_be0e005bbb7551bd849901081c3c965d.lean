import Mathlib

theorem number_theory_876 (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (hmn : m > n) (h : 100 ∣ (2 ^ m - 1) + (2 ^ n - 1)) :
    (2 ^ m - 1) ≥ 2 ^ 12 + 1 := by
  by_contra h1
  push_neg at h1
  have h2 : m ≤ 12 := by 
    by_contra h2
    push_neg at h2
    have h3 : 2 ^ m ≥ 2 ^ 13 := by 
      have h4 : m ≥ 13 := by linarith 
      exact Nat.pow_le_pow_of_le_right (by norm_num) h4 
    have h4 : (2 ^ m - 1 : ℕ) ≥ 2 ^ 13 - 1 := by 
      omega 
    omega 
  have h3 : n ≤ 11 := by 
    omega 
  interval_cases m <;> interval_cases n <;> norm_num at h <;> omega