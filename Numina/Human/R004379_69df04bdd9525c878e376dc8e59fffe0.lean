import Mathlib

theorem number_theory_258749 (a : ℤ) (ha : a^100 % 73 = 2) (hb : a^101 % 73 = 69) :
    a % 73 = 71 := by
  have h1 : a^101 % 73 = (a^100 * a) % 73 := by 
    ring_nf
  rw [h1] at hb
  rw [Int.mul_emod, ha] at hb
  omega