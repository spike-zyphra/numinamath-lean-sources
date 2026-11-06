import Mathlib

theorem number_theory_4956_1
    (a b : ℤ)
    (ha : a % 2 = 1) (hb : b % 2 = 1)
    : (a * b) % 2 = 1 := by
  -- the product of two odd integers is odd
  simp [Int.mul_emod, ha, hb]

theorem number_theory_4956_2
    (a b : ℤ)
    (h : a % 2 = 0 ∨ b % 2 = 0)
    : (a * b) % 2 = 0 := by 
  rcases h with (ha | hb)
  · -- Case where a % 2 = 0 
    simp [Int.mul_emod, ha]
  · -- Case where b % 2 = 0
    simp [Int.mul_emod, hb]