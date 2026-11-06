import Mathlib

theorem number_theory_319937 (a b : ℤ) (ha : a % 7 = 3) (hb : b % 7 = 5)
    (h : a^2 > 4 * b) :
    (a^2 - 4 * b) % 7 = 3 := by

  have h1 : a^2 % 7 = 2 := by
    have h2 : a % 7 = 3 := ha
    simp [pow_two, Int.add_emod, Int.mul_emod, h2, Int.ofNat, Int.emod_self]
    <;> omega

  have h2 : (4 * b) % 7 = 6 := by 
    have h3 : b % 7 = 5 := hb
    simp [Int.add_emod, Int.mul_emod, h3, Int.ofNat, Int.emod_self]
    <;> omega

  omega