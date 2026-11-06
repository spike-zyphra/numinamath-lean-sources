import Mathlib

theorem number_theory_173213 (a b c : ℤ) : 30 ∣ a + b + c → 30 ∣ a^5 + b^5 + c^5 := by 
  intro h
  have h4 : (a ^ 5 + b ^ 5 + c ^ 5) % 2 = 0 := by
    have h1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have h2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    have h3 : c % 2 = 0 ∨ c % 2 = 1 := by omega
    rcases h1 with (h1 | h1)
    <;> rcases h2 with (h2 | h2)
    <;> rcases h3 with (h3 | h3)
    <;> simp [Int.add_emod, Int.mul_emod, pow_succ, h1, h2, h3]
    <;> omega
  have h4' : (a ^ 5 + b ^ 5 + c ^ 5) % 3 = 0 := by
    have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    have h3 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
    rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3)
    <;> simp [Int.add_emod, Int.mul_emod, pow_succ, h1, h2, h3]
    <;> omega
  have h4'' : (a ^ 5 + b ^ 5 + c ^ 5) % 5 = 0 := by
    have h1 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
    have h2 : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
    have h3 : c % 5 = 0 ∨ c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3 | h3 | h3)
    <;> simp [Int.add_emod, Int.mul_emod, pow_succ, h1, h2, h3]
    <;> omega
  omega