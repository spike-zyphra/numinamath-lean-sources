import Mathlib

theorem number_theory_309316 (a b : ℤ) (h : 3 ∣ a^2 + b^2) : 3 ∣ a ∧ 3 ∣ b := by
  have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
    omega
  have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
    omega
  have h3 : (a ^ 2 + b ^ 2) % 3 = 0 := by
    omega
  rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1, h2] at h3 <;> 
    omega