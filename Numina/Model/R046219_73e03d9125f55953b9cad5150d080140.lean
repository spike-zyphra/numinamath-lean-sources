import Mathlib

theorem number_theory_2670
    (a b c : ℤ)
    (h₀ : 6 ∣ a + b + c) :
    0 = (a^3 + b^3 + c^3) % 6 := by

  have h1 : a^3 % 6 = a % 6 := by
    have h2 : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h2]

  have h2 : b^3 % 6 = b % 6 := by 
    have h3 : b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by 
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h3]

  have h3 : c^3 % 6 = c % 6 := by 
    have h4 : c % 6 = 0 ∨ c % 6 = 1 ∨ c % 6 = 2 ∨ c % 6 = 3 ∨ c % 6 = 4 ∨ c % 6 = 5 := by 
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h4]

  -- Show $a^3 \equiv a \pmod{6}$ implies $a^3 + b^3 + c^3 \equiv a + b + c \pmod{6}$.
  have h4 : (a^3 + b^3 + c^3) % 6 = (a + b + c) % 6 := by 
    simp [Int.add_emod, h1, h2, h3]

  have h5 : (a + b + c) % 6 = 0 := by 
    omega

  -- Transitivity of congruence.
  rw [h4, h5]
  all_goals omega