import Mathlib

theorem number_theory_151236 (a b : ℤ) (h : 9 ∣ a^2 + a * b + b^2) :
    3 ∣ a ∧ 3 ∣ b := by
  have h1 : a % 9 = 0 ∨ a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 3 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨ a % 9 = 6 ∨ a % 9 = 7 ∨ a % 9 = 8 := by
    omega
  have h2 : b % 9 = 0 ∨ b % 9 = 1 ∨ b % 9 = 2 ∨ b % 9 = 3 ∨ b % 9 = 4 ∨ b % 9 = 5 ∨ b % 9 = 6 ∨ b % 9 = 7 ∨ b % 9 = 8 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
    ( norm_num [Int.dvd_iff_emod_eq_zero, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h1, h2] at h <;> omega )