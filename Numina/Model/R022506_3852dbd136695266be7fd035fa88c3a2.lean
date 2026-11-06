import Mathlib

theorem number_theory_213111 (n : ℕ) (h : n > 0) (h' : 115 = 15 * n + 11 * (n - 1)) :
    n = 9 := by 
  by_cases h1 : n ≤ 7
  · -- Assume n ≤ 7, so n ≤ 7.
    interval_cases n <;> omega
  · -- Assume n > 7, so n ≥ 8.
    have h2 : n ≥ 8 := by 
      omega
    have h3 : 15 * n + 11 * (n - 1) > 115 := by 
      have h4 : n - 1 ≥ 7 := by 
        omega
      have h5 : 15 * n ≥ 120 := by 
        omega
      have h6 : 11 * (n - 1) ≥ 77 := by 
        omega
      omega 
    omega