import Mathlib

theorem number_theory_234507 (x y z : ℤ) :
    (x - y)^3 + (y - z)^3 + (z - x)^3 ≠ 2011 := by
  intro h
  have h2 : ((x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 : ℤ) % 3 = 0 := by 
    have h_eq_zero : ((x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 : ℤ) % 3 = 0 := by
      have h10 : (x : ℤ) % 3 = 0 ∨ (x : ℤ) % 3 = 1 ∨ (x : ℤ) % 3 = 2 := by 
        omega
      have h11 : (y : ℤ) % 3 = 0 ∨ (y : ℤ) % 3 = 1 ∨ (y : ℤ) % 3 = 2 := by 
        omega
      have h12 : (z : ℤ) % 3 = 0 ∨ (z : ℤ) % 3 = 1 ∨ (z : ℤ) % 3 = 2 := by 
        omega
      rcases h10 with h10 | h10 | h10 <;> rcases h11 with h11 | h11 | h11 <;> rcases h12 with h12 | h12 | h12 <;> 
        simp [Int.add_emod, Int.mul_emod, pow_three, Int.sub_emod, h10, h11, h12] <;> omega
    omega
  have h3 : ((x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 : ℤ) % 3 = 2011 % 3 := by
    rw [h]
  norm_num at h3
  omega