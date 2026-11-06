import Mathlib

theorem algebra_232650 : ¬∃ x y : ℤ, x^3 + 6 * x^2 + 5 * x = y^3 - y + 2 := by
  rintro ⟨x, y, h⟩
  have h1 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by
    omega
  have h2 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by
    omega
  have eq1 : (x^3 + 6 * x^2 + 5 * x) % 9 = (y^3 - y + 2) % 9 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
  rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
  simp [pow_succ, pow_zero, Int.add_emod, Int.sub_emod, Int.mul_emod, h1, h2] at eq1
  <;> omega