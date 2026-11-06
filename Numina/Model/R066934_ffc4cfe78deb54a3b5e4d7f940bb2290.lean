import Mathlib

theorem number_theory_27428 : ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 - 8 * c = 6 := by
  rintro ⟨a, b, c, h⟩
  have h1 : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
    have h1 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h] at *
  have h2 : b^2 % 8 = 0 ∨ b^2 % 8 = 1 ∨ b^2 % 8 = 4 := by
    have h1 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h] at *
  have h3 : (a^2 + b^2) % 8 = 6 % 8 := by
    omega
  omega