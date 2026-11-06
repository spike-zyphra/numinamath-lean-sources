import Mathlib

theorem number_theory_116181 : ¬∃ a b : ℤ, 4 ∣ a^2 + b^2 + 1 := by
  intro h
  rcases h with ⟨a, b, hdiv⟩
  have h1 : a^2 % 4 = 0 ∨ a^2 % 4 = 1 := by 
    have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1)
    · simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    · simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    · simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    · simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    all_goals omega
  have h2 : b^2 % 4 = 0 ∨ b^2 % 4 = 1 := by 
    have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2)
    · simp [pow_two, Int.add_emod, Int.mul_emod, h2]
    · simp [pow_two, Int.add_emod, Int.mul_emod, h2]
    · simp [pow_two, Int.add_emod, Int.mul_emod, h2]
    · simp [pow_two, Int.add_emod, Int.mul_emod, h2]
    all_goals omega
  have h3 : (a^2 + b^2 + 1) % 4 = 0 := by 
    omega
  omega