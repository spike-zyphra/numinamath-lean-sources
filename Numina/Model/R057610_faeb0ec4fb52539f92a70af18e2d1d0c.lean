import Mathlib

theorem number_theory_47750 : ¬∃ a b : ℤ, a > 0 ∧ b > 0 ∧ a^3 - b^3 = 2004 := by
  rintro ⟨a, b, ha, hb, h⟩
  have h1 : a^3 % 9 = 0 ∨ a^3 % 9 = 1 ∨ a^3 % 9 = 8 := by
    have h2 : a % 9 = 0 ∨ a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 3 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨ a % 9 = 6 ∨ a % 9 = 7 ∨ a % 9 = 8 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h | h) <;> 
      norm_num [pow_succ, Int.mul_emod, h] at *
  have h2 : b^3 % 9 = 0 ∨ b^3 % 9 = 1 ∨ b^3 % 9 = 8 := by
    have h3 : b % 9 = 0 ∨ b % 9 = 1 ∨ b % 9 = 2 ∨ b % 9 = 3 ∨ b % 9 = 4 ∨ b % 9 = 5 ∨ b % 9 = 6 ∨ b % 9 = 7 ∨ b % 9 = 8 := by 
      omega
    rcases h3 with (h | h | h | h | h | h | h | h | h) <;> 
      norm_num [pow_succ, Int.mul_emod, h] at *
  -- Now we compute the residue of a^3 - b^3.
  -- Since a^3 ≡ 0, 1, or 8 (mod 9) and b^3 ≡ 0, 1, or 8 (mod 9)
  -- Thus a^3 - b^3 ≡ 0, ±1, ±2, ±7, ±8 (mod 9)
  -- But 2004 ≡ 6 (mod 9)
  omega