import Mathlib

theorem number_theory_7990 (x y : ℤ) : ¬ (x^2 + 3 * x * y - 2 * y^2 = 122) := by
  rintro h
  have h1 : (x ^ 2 + 3 * x * y - 2 * y ^ 2 : ℤ) % 17 = 122 % 17 := by 
    omega
  have h2 : (x ^ 2 + 3 * x * y - 2 * y ^ 2 : ℤ) % 17 = 
    ((x % 17) ^ 2 + 3 * (x % 17) * (y % 17) - 2 * (y % 17) ^ 2 : ℤ) % 17 := by
    simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two]
    <;> ring_nf
    <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two]
    all_goals omega
  have h3 : ((x % 17) ^ 2 + 3 * (x % 17) * (y % 17) - 2 * (y % 17) ^ 2 : ℤ) % 17 = 3 := by 
    omega
  have h4 : x % 17 = 0 ∨ x % 17 = 1 ∨ x % 17 = 2 ∨ x % 17 = 3 ∨ x % 17 = 4 ∨ x % 17 = 5 ∨ x % 17 = 6 ∨ x % 17 = 7 ∨ x % 17 = 8 ∨ x % 17 = 9 ∨ x % 17 = 10 ∨ x % 17 = 11 ∨ x % 17 = 12 ∨ x % 17 = 13 ∨ x % 17 = 14 ∨ x % 17 = 15 ∨ x % 17 = 16 := by
    omega
  have h5 : y % 17 = 0 ∨ y % 17 = 1 ∨ y % 17 = 2 ∨ y % 17 = 3 ∨ y % 17 = 4 ∨ y % 17 = 5 ∨ y % 17 = 6 ∨ y % 17 = 7 ∨ y % 17 = 8 ∨ y % 17 = 9 ∨ y % 17 = 10 ∨ y % 17 = 11 ∨ y % 17 = 12 ∨ y % 17 = 13 ∨ y % 17 = 14 ∨ y % 17 = 15 ∨ y % 17 = 16 := by
    omega
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, h4, h5, pow_two] at h3 <;> omega