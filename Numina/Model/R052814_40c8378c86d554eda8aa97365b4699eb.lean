import Mathlib

theorem number_theory_226959 {n : ℕ} (hn : n > 0) (h : 43 * n + 70 * n + 57 * n = 20172 - 20172 % 100) :
    n = 4 := by 
  omega