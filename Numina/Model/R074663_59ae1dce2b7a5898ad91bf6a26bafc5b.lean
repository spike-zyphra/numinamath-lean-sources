import Mathlib

theorem number_theory_173171 (x y : ℤ) : ¬ x^2 - 7 * y = 10 := by 
  intro h
  have h1 : x^2 % 7 = 0 ∨ x^2 % 7 = 1 ∨ x^2 % 7 = 2 ∨ x^2 % 7 = 4 := by 
    have h1 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h1] at *
  have h2 : (x^2 - 7 * y) % 7 = 10 % 7 := by 
    omega
  omega