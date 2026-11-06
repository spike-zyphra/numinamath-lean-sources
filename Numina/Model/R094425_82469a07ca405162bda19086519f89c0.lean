import Mathlib

open Real
open scoped BigOperators

theorem number_theory_8692 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
  : ¬ (x^2 + 8 * z = 3 + 2 * y^2) := by 
  rintro h
  have h1 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by
    have h2 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
      norm_num [Int.add_emod, Int.mul_emod, pow_two, h2] at *
  
  have h3 : (y^2 % 8 = 0 ∨ y^2 % 8 = 1 ∨ y^2 % 8 = 4) := by 
    have h2 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
      norm_num [Int.add_emod, Int.mul_emod, pow_two, h2] at *
  
  have h4 : x^2 % 8 = (3 + 2 * (y^2 : ℤ)) % 8 := by 
    omega

  omega