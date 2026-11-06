import Mathlib

theorem number_theory_308900 (x y : ℤ) : ¬ (x^2 + y^2 = 1995) := by 
  rintro h
  have h1 : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by
    have h11 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by
      omega
    rcases h11 with (h11 | h11 | h11 | h11)
    · -- x % 4 = 0
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h11]
    · -- x % 4 = 1
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h11]
    · -- x % 4 = 2
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h11]
    · -- x % 4 = 3
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h11]
  have h2 : y^2 % 4 = 0 ∨ y^2 % 4 = 1 := by
    have h21 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by
      omega
    rcases h21 with (h21 | h21 | h21 | h21)
    · -- y % 4 = 0
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h21]
    · -- y % 4 = 1
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h21]
    · -- y % 4 = 2
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h21]
    · -- y % 4 = 3
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h21]
  have h3 : (x^2 + y^2) % 4 = 3 := by
    omega
  omega
  all_goals try tauto
  all_goals try nlinarith