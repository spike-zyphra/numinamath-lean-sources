import Mathlib

theorem number_theory_35280 : ¬∃ x y : ℤ, x^2 + 3 * x * y - 2 * y^2 = 122 := by
  rintro ⟨x, y, h_eq⟩
  have eq1 : (2 * x + 3 * y) ^ 2 - (17 * y ^ 2) = 488 := by
    nlinarith [sq_nonneg (x * 2), sq_nonneg ((3 * y - 2 * x) ), sq_nonneg (2 * x - 3 * y), sq_nonneg (y * 2), sq_nonneg ((x + y) * 3), sq_nonneg ((y - x) * 3)]
  have eq3 : (2 * x + 3 * y) ^ 2 % 17 = 12 % 17 := by
    omega
  have h2 : (2 * x + 3 * y) % 17 = 0 ∨ (2 * x + 3 * y) % 17 = 1 ∨ (2 * x + 3 * y) % 17 = 2 ∨ (2 * x + 3 * y) % 17 = 3 ∨ (2 * x + 3 * y) % 17 = 4 ∨ (2 * x + 3 * y) % 17 = 5 ∨ (2 * x + 3 * y) % 17 = 6 ∨ (2 * x + 3 * y) % 17 = 7 ∨ (2 * x + 3 * y) % 17 = 8 ∨ (2 * x + 3 * y) % 17 = 9 ∨ (2 * x + 3 * y) % 17 = 10 ∨ (2 * x + 3 * y) % 17 = 11 ∨ (2 * x + 3 * y) % 17 = 12 ∨ (2 * x + 3 * y) % 17 = 13 ∨ (2 * x + 3 * y) % 17 = 14 ∨ (2 * x + 3 * y) % 17 = 15 ∨ (2 * x + 3 * y) % 17 = 16 := by 
    omega
  rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h2, Int.add_emod, Int.mul_emod] at eq3