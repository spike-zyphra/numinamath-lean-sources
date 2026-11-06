import Mathlib

theorem number_theory_36116 : ¬∃ (x y : ℤ), x^2 - y^2 = 2006 := by 
  rintro ⟨x, y, h⟩
  have h1 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by
    have h2 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h2]
  have h2 : y^2 % 8 = 0 ∨ y^2 % 8 = 1 ∨ y^2 % 8 = 4 := by 
    have h3 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by 
      omega 
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h3]
  -- Given h: x^2 - y^2 = 2006, so x^2 - y^2 ≡ 6 (mod 8)
  -- But by h1 and h2, we know x^2 ≡0,1,4 and y^2 ≡0,1,4
  -- So x^2 - y^2 ≡0,1,3,4,5,7 (mod8). 6 ≡ x^2 - y^2 (mod8)
  -- Therefore, contradiction
  omega