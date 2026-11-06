import Mathlib

theorem number_theory_69444 : ¬∃ (x y z : ℤ), x > 0 ∧ y > 0 ∧ z > 0 ∧ x^2 + 8 * z = 3 + 2 * y^2 := by 
  rintro ⟨x, y, z, hx, hy, hz, heq⟩
  have h_eq_mod_8 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by 
    have h1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
  have h_eq_mod_8_y2 : y^2 % 8 = 0 ∨ y^2 % 8 = 1 ∨ y^2 % 8 = 4 := by 
    have h1 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by 
      omega 
    rcases h1 with (h | h | h | h | h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
  -- heq
  have h_eq1 : x^2 % 8 = (3 + 2 * (y^2)) % 8 := by
    omega
  -- contradiction
  omega 
  all_goals
  omega