import Mathlib

theorem number_theory_237213 : ¬ ∃ x y : ℤ, x^2 + 3 * x * y - 2 * y^2 = 122 := by
  rintro ⟨x, y, h_eq⟩

  have h1 : (2 * x + 3 * y) ^ 2 = 17 * y ^ 2 + 488 := by 
    nlinarith

  have h2 : (2 * x + 3 * y) ^ 2 % 17 = 12 := by 
    omega
  have h_sq_nonres : (2 * x + 3 * y) ^ 2 % 17 = 0 ∨ (2 * x + 3 * y) ^ 2 % 17 = 1 ∨ 
      (2 * x + 3 * y) ^ 2 % 17 = 2 ∨ (2 * x + 3 * y) ^ 2 % 17 = 4 ∨
      (2 * x + 3 * y) ^ 2 % 17 = 8 ∨ (2 * x + 3 * y) ^ 2 % 17 = 9 ∨
      (2 * x + 3 * y) ^ 2 % 17 = 13 ∨ (2 * x + 3 * y) ^ 2 % 17 = 15 ∨
      (2 * x + 3 * y) ^ 2 % 17 = 16 := by
    have h : (2 * x + 3 * y) % 17 = 0 ∨ (2 * x + 3 * y) % 17 = 1 ∨ (2 * x + 3 * y) % 17 = 2 ∨ (2 * x + 3 * y) % 17 = 3 ∨ (2 * x + 3 * y) % 17 = 4 ∨ (2 * x + 3 * y) % 17 = 5 ∨ (2 * x + 3 * y) % 17 = 6 ∨ (2 * x + 3 * y) % 17 = 7 ∨ (2 * x + 3 * y) % 17 = 8 ∨ (2 * x + 3 * y) % 17 = 9 ∨ (2 * x + 3 * y) % 17 = 10 ∨ (2 * x + 3 * y) % 17 = 11 ∨ (2 * x + 3 * y) % 17 = 12 ∨ (2 * x + 3 * y) % 17 = 13 ∨ (2 * x + 3 * y) % 17 = 14 ∨ (2 * x + 3 * y) % 17 = 15 ∨ (2 * x + 3 * y) % 17 = 16 := by
      omega
    rcases h with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h]
    <;> omega

  omega