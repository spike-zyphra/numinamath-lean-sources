import Mathlib

theorem number_theory_81641 :
    ∀ n : ℕ, ∃ m : ℕ, m > n ∧ ¬∃ a b c : ℤ, m = a^4 + b^4 + c^4 := by
  intro n
  use 8 * n + 7
  constructor
  · -- Show m > n
    omega
  · -- Show that $8n + 7$ cannot be written as a^4 + b^4 + c^4
    intro h
    rcases h with ⟨a, b, c, h_eq⟩
    have h1 : ( (8 * (n : ℤ) + 7) : ℤ ) = a^4 + b^4 + c^4 := by
      omega
    have h2 : (a^4 + b^4 + c^4 : ℤ) % 8 = 7 % 8 := by 
      omega
    have h3 : (a^4 % 8) = 0 ∨ (a^4 % 8) = 1 := by 
      have h2 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2)
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h2]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h2]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h2]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h2]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h2]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h2]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h2]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h2]
    have h4 : (b^4 % 8) = 0 ∨ (b^4 % 8) = 1 := by 
      have h3 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by 
        omega
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3)
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
    have h5 : (c^4 % 8) = 0 ∨ (c^4 % 8) = 1 := by 
      have h4 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by 
        omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4)
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
      · simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
    omega