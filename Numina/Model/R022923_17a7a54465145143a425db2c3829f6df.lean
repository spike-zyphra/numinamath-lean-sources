import Mathlib

theorem algebra_183588 (n : ℕ) (h : n * (n + 1) * (n + 2) = (n + (n + 1) + (n + 2)) * 65) :
    n = 13 := by 
  have h1 : n * (n + 1) * (n + 2) = (3 * (n + 1)) * 65 := by 
    have h_sum : n + (n + 1) + (n + 2) = 3 * (n + 1) := by
      omega
    rw [h_sum] at h 
    linarith
  have h2 : n ≤ 20 := by
    nlinarith [sq_nonneg ((n : ℤ) - 13), sq_nonneg ((n : ℤ) + 14), sq_nonneg ((n : ℤ) - 15)]
  interval_cases n <;> omega