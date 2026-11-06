import Mathlib

theorem number_theory_145299 (a : ℕ) (ha : a = 111 + 22 + 2 + 555) :
    a % 10 = 0 := by
  calc 
    a % 10 = (111 + 22 + 2 + 555) % 10 := by rw [ha]
    _ = 690 % 10 := by norm_num
    _ = 0 := by norm_num