import Mathlib

theorem number_theory_302797 : ¬∃ x y, x^2 - y^2 = 2006 := by
  rintro ⟨x, y, h⟩
  have h1 : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by
    have h2 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [pow_two, Nat.mul_mod, Nat.add_mod, h2] 
      <;> omega
  have h2 : y^2 % 4 = 0 ∨ y^2 % 4 = 1 := by
    have h3 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by 
      omega
    rcases h3 with (h3 | h3 | h3 | h3) <;> simp [pow_two, Nat.mul_mod, Nat.add_mod, h3] 
      <;> omega
  omega