import Mathlib

theorem number_theory_258327 (a b : ℤ) : 6 ∣ a + b ↔ 6 ∣ a^3 + b^3 := by 
  constructor
  · -- Assume 6 divides a + b, prove 6 divides a^3 + b^3
    intro h
    have h1 : a^3 % 6 = a % 6 := by
      have h2 : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
    have h2 : b^3 % 6 = b % 6 := by
      have h3 : b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by
        omega
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, pow_succ, Int.add_emod, Int.mul_emod]
    have : (a^3 + b^3) % 6 = (a + b) % 6 := by 
      omega
    omega
  · -- Assume 6 divides a^3 + b^3, prove 6 divides a + b
    intro h
    have h1 : a^3 % 6 = a % 6 := by
      have h2 : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
    have h2 : b^3 % 6 = b % 6 := by
      have h3 : b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by
        omega
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, pow_succ, Int.add_emod, Int.mul_emod]
    have : (a^3 + b^3) % 6 = (a + b) % 6 := by
      omega
    omega