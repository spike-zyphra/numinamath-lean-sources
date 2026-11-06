import Mathlib

/-
Show that the product of two odd integers is odd
-/
theorem number_theory_4956_1
    (a b : ℤ)
    (ha : a % 2 = 1) (hb : b % 2 = 1)
    : (a * b) % 2 = 1 := by
  -- the product of two odd integers is odd
  simp [Int.mul_emod, ha, hb]

/-
while the product of two integers is even if either of the integers is even
-/
theorem number_theory_4956_2
    (a b : ℤ)
    (h : a % 2 = 0 ∨ b % 2 = 0)
    : (a * b) % 2 = 0 := by
  -- the product of two integers is even if either of the integers is even
  rcases h with h | h
  . simp [Int.mul_emod, h]
  . simp [Int.mul_emod, h]
