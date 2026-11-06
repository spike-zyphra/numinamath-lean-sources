import Mathlib

theorem inequalities_292332 (n : ℤ) : 6 * n ^ 2 - 7 * n + 2 > 0 := by
  have h1 : 6 * n ^ 2 - 7 * n + 2 = (3 * n - 2) * (2 * n - 1) := by
    ring
  rw [h1]
  by_cases h : n ≥ 1
  · 
    have h2 : 3 * n - 2 > 0 := by
      omega
    have h3 : 2 * n - 1 > 0 := by
      omega
    nlinarith
  · 
    have h4 : n ≤ 0 := by
      omega
    have h5 : 3 * n - 2 < 0 := by
      nlinarith 
    have h6 : 2 * n - 1 < 0 := by
      nlinarith
    nlinarith