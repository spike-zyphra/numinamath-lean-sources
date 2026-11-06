import Mathlib

theorem number_theory_253570 (y : ℕ) (hy : y < 100) (h : y + (Nat.digits 10 y).sum = 2023) :
    y = 19 := by 
  interval_cases y <;> norm_num at h 
  <;> omega