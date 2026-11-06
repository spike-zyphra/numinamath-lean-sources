import Mathlib

theorem number_theory_126970 : ¬∃ (a b c : ℤ), a^2 + b^2 - 8 * c = 6 := by
  rintro ⟨a, b, c, h⟩
  have h1 : (a^2 : ℤ) % 8 = 0 ∨ (a^2 : ℤ) % 8 = 1 ∨ (a^2 : ℤ) % 8 = 4 := by
    have h2 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h2]
  
  have h2 : (b^2 : ℤ) % 8 = 0 ∨ (b^2 : ℤ) % 8 = 1 ∨ (b^2 : ℤ) % 8 = 4 := by
    have h3 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h3]
  
  omega