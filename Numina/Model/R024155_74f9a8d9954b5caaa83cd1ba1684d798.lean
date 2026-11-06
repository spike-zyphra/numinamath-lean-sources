import Mathlib

theorem number_theory_69162 : ¬∃ a b c : ℤ, a^2 * b^2 + b^2 * c^2 + 3 * b^2 - c^2 - a^2 = 2005 := by
  rintro ⟨a, b, c, h⟩
  have eq1 : (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + 3 * b ^ 2 - c ^ 2 - a ^ 2) % 4 = 2005 % 4 := by
    omega
  have h1 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
    omega
  have h2 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by
    omega
  have h3 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by
    omega
  have h11 : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
    rcases h2 with (h2 | h2 | h2 | h2) <;> 
    ( 
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h2, Int.emod] 
    )
  have h12 : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
    rcases h1 with (h1 | h1 | h1 | h1) <;> 
    ( 
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h1, Int.emod] 
    )
  have h13 : c ^ 2 % 4 = 0 ∨ c ^ 2 % 4 = 1 := by
    rcases h3 with (h3 | h3 | h3 | h3) <;> 
    ( 
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h3, Int.emod] 
    )
  rcases h1 with (h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3 | h3) <;> 
    ( 
      simp [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_two, h1, h2, h3, Int.emod] at eq1 ⊢
      <;> omega
    )