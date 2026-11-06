import Mathlib

theorem number_theory_225499 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x^2 - 2 * y^2 + 8 * z = 3) :
    False := by 
  have h1 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by 
    have h1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h1] at *
  have h2 : y^2 % 8 = 0 ∨ y^2 % 8 = 1 ∨ y^2 % 8 = 4 := by 
    have h2 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
      norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h2] at *
  have h3 : (x ^ 2 - 2 * y ^ 2) % 8 = 3 % 8 := by 
    omega 
  have h4 : (x ^ 2 - 2 * y ^ 2) % 8 = 0 ∨ (x ^ 2 - 2 * y ^ 2) % 8 = 1 ∨ (x ^ 2 - 2 * y ^ 2) % 8 = 2 ∨ (x ^ 2 - 2 * y ^ 2) % 8 = 4 ∨ (x ^ 2 - 2 * y ^ 2) % 8 = 6 ∨ (x ^ 2 - 2 * y ^ 2) % 8 = 7 := by 
    rcases h1 with (hx | hx | hx)
    <;> rcases h2 with (hy | hy | hy)
    <;> omega
  omega