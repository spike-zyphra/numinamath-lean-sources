import Mathlib

theorem number_theory_232347 (n : ℕ) (h : n > 0) (h1 : n % 10 * 17 = n) :
    n = 85 := by
  have h3 : n ≤ 9 * 17 := by
    have h3 : n % 10 * 17 = n := h1
    have h4 : n % 10 ≤ 9 := by
      omega
    -- Now n ≤ 9 * 17
    nlinarith [h3, h4]
  have h4 : n ≤ 153 := by norm_num at h3 ⊢; exact h3
  interval_cases n <;> omega