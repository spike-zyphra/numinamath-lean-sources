import Mathlib

theorem number_theory_283782 (x : ℕ) (h : x * 50 = 10000) : x = 200 := by
  have h1 : x = 200 := by 
    omega
  exact h1