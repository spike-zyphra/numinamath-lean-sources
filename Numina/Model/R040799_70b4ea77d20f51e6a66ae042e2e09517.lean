import Mathlib

theorem number_theory_291629 (a b : ℤ) : 30 ∣ a * b * (a^4 - b^4) := by
  have h1 : a * b * (a ^ 4 - b ^ 4) % 2 = 0 := by
    have h1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have h2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> simp [h1, h2, 
      Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ, Int.sub_emod, Int.add_emod]
  have h2 : a * b * (a ^ 4 - b ^ 4) % 3 = 0 := by
    have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> simp [h1, h2, 
      Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ, Int.sub_emod, Int.add_emod]
  have h3 : a * b * (a ^ 4 - b ^ 4) % 5 = 0 := by
    have h1 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
    have h2 : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> simp [h1, h2, 
      Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ, Int.sub_emod, Int.add_emod]
  omega