import Mathlib

theorem number_theory_96496 (B : ℕ) (hB : B < 10) (h : (B * 10 + 2) * (70 + B) = 6396) :
    B = 8 := by 
  interval_cases B <;> omega