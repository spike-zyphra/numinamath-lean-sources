import Mathlib

theorem number_theory_309228 {a b : ℤ} (ha : a % 7 = 3) (hb : b % 7 = 5)
    (h : a^2 > 4 * b) :
    (a^2 - 4 * b) % 7 = 3 := by 
  have ha2 : a^2 % 7 = 2 := by 
    have : a % 7 = 3 := ha
    simp [pow_two, Int.mul_emod, this]
  have hb2 : 4 * b % 7 = 6 := by 
    have : b % 7 = 5 := hb
    simp [Int.mul_emod, this]
  have key : (a^2 - 4 * b) % 7 = 3 := by 
    omega
  exact key