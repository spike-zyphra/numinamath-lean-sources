import Mathlib

theorem number_theory_190520 (n : ℕ) (h : n > 0) (h1 : (12 * n) / 100 > 5 * n / 100)
    (h2 : (12 * n) / 100 = 25 * n / 100 + (12 * n - 25 * n) / 100) :
    (12 * n) / 100 ≤ 50 := by 
  omega