import Mathlib

theorem number_theory_290282 (n : ℕ) (hn : n ≠ 0) (h : 76 * n / 100 + 24 * n / 100 = n) :
    n ≥ 25 := by 
  by_contra h1
  push_neg at h1
  interval_cases n <;> omega