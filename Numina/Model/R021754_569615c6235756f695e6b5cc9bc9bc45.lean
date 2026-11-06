import Mathlib

theorem number_theory_208450 (a b c : ℕ) (h : 28*a + 30*b + 31*c = 365) : a + b + c = 12 := by
  have h1 : a ≤ 12 := by
    omega
  have h2 : b ≤ 12 := by 
    omega
  have h3 : c ≤ 12 := by 
    omega
  interval_cases a <;> interval_cases b <;> omega