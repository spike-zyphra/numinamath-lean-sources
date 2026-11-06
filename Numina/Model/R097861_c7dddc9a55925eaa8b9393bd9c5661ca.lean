import Mathlib

theorem number_theory_235772 (a b : ℕ) (ha : a = 17) (hb : b = 39) :
    b - a - 1 = 21 := by 
  calc
    b - a - 1 = 39 - 17 - 1 := by rw [hb, ha] -- Substitute the values of a and b
    _ = 22 - 1 := by norm_num -- Compute 39 - 17 = 22
    _ = 21 := by norm_num -- Compute 22 - 1 = 21