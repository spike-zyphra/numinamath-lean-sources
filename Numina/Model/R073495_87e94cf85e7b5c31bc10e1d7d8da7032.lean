import Mathlib

theorem inequalities_42270 (n : ℕ) (hn : n ≤ 100) (h : 7 * n - 8 * (100 - n) ≥ 10 * n - 10 * (100 - n)) :
    n ≤ 81 := by 
  omega