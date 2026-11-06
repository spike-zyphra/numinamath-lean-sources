import Mathlib

theorem number_theory_285855 (a b c : ℤ) (ha : a < c) (h : a^2 + c^2 = 2 * b^2) :
    48 ∣ c^2 - a^2 := by
  have h1 : (c ^ 2 - a ^ 2) % 16 = 0 := by
    have h2 : (a ^ 2 : ℤ) % 16 = (c ^ 2 : ℤ) % 16 := by
      have h1 : (a ^ 2 + c ^ 2 : ℤ) % 16 = (2 * b ^ 2 : ℤ) % 16 := by 
        omega
      have h4 : (a ^ 2 : ℤ) % 16 = 0 ∨ (a ^ 2 : ℤ) % 16 = 1 ∨ (a ^ 2 : ℤ) % 16 = 4 ∨ (a ^ 2 : ℤ) % 16 = 9 := by 
        have h10 : a % 16 = 0 ∨ a % 16 = 1 ∨ a % 16 = 2 ∨ a % 16 = 3 ∨ a % 16 = 4 ∨ a % 16 = 5 ∨ a % 16 = 6 ∨ a % 16 = 7 ∨ a % 16 = 8 ∨ a % 16 = 9 ∨ a % 16 = 10 ∨ a % 16 = 11 ∨ a % 16 = 12 ∨ a % 16 = 13 ∨ a % 16 = 14 ∨ a % 16 = 15 := by
          omega
        rcases h10 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> 
          simp [pow_two, Int.add_emod, Int.mul_emod, h]
      have h4' : (c ^ 2 : ℤ) % 16 = 0 ∨ (c ^ 2 : ℤ) % 16 = 1 ∨ (c ^ 2 : ℤ) % 16 = 4 ∨ (c ^ 2 : ℤ) % 16 = 9 := by 
        have h10 : c % 16 = 0 ∨ c % 16 = 1 ∨ c % 16 = 2 ∨ c % 16 = 3 ∨ c % 16 = 4 ∨ c % 16 = 5 ∨ c % 16 = 6 ∨ c % 16 = 7 ∨ c % 16 = 8 ∨ c % 16 = 9 ∨ c % 16 = 10 ∨ c % 16 = 11 ∨ c % 16 = 12 ∨ c % 16 = 13 ∨ c % 16 = 14 ∨ c % 16 = 15 := by
          omega
        rcases h10 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> 
          simp [pow_two, Int.add_emod, Int.mul_emod, h]
      have h4'' : (b ^ 2 : ℤ) % 16 = 0 ∨ (b ^ 2 : ℤ) % 16 = 1 ∨ (b ^ 2 : ℤ) % 16 = 4 ∨ (b ^ 2 : ℤ) % 16 = 9 := by 
        have h10 : b % 16 = 0 ∨ b % 16 = 1 ∨ b % 16 = 2 ∨ b % 16 = 3 ∨ b % 16 = 4 ∨ b % 16 = 5 ∨ b % 16 = 6 ∨ b % 16 = 7 ∨ b % 16 = 8 ∨ b % 16 = 9 ∨ b % 16 = 10 ∨ b % 16 = 11 ∨ b % 16 = 12 ∨ b % 16 = 13 ∨ b % 16 = 14 ∨ b % 16 = 15 := by
          omega
        rcases h10 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> 
          simp [pow_two, Int.add_emod, Int.mul_emod, h]
      omega
    omega
  have h3 : (c ^ 2 - a ^ 2) % 3 = 0 := by
    have h1 : (a ^ 2 + c ^ 2 : ℤ) % 3 = (2 * b ^ 2 : ℤ) % 3 := by 
      omega
    have h2 : (a ^ 2 : ℤ) % 3 = 0 ∨ (a ^ 2 : ℤ) % 3 = 1 := by
      have h10 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
        omega
      rcases h10 with (h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h]
    have h2' : (c ^ 2 : ℤ) % 3 = 0 ∨ (c ^ 2 : ℤ) % 3 = 1 := by
      have h10 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by
        omega
      rcases h10 with (h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h]
    have h2'' : (b ^ 2 : ℤ) % 3 = 0 ∨ (b ^ 2 : ℤ) % 3 = 1 := by 
      have h10 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
        omega
      rcases h10 with (h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h]
    omega
  omega