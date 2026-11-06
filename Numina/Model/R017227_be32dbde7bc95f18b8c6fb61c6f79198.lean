import Mathlib

theorem number_theory_69918 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 30 ∣ a + b + c) : 30 ∣ a^5 + b^5 + c^5 := by
  have h1 : (a ^ 5 + b ^ 5 + c ^ 5) % 2 = 0 := by
    have h2 : (a + b + c) % 2 = 0 := by
      omega
    have h3 : a % 2 = 0 ∨ a % 2 = 1 := by
      omega
    have h4 : b % 2 = 0 ∨ b % 2 = 1 := by 
      omega
    have h5 : c % 2 = 0 ∨ c % 2 = 1 := by
      omega
    have h_eq1 : a ^ 5 % 2 = a % 2 := by 
      rcases h3 with (h3 | h3) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
    have h_eq2 : b ^ 5 % 2 = b % 2 := by 
      rcases h4 with (h4 | h4) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
    have h_eq3 : c ^ 5 % 2 = c % 2 := by 
      rcases h5 with (h5 | h5) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h5]
    omega

  have h1' : (a ^ 5 + b ^ 5 + c ^ 5) % 3 = 0 := by
    have h2 : (a + b + c) % 3 = 0 := by
      omega
    have h3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
      omega
    have h4 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
      omega
    have h5 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by
      omega
    have h_eq1 : a ^ 5 % 3 = a % 3 := by 
      rcases h3 with (h3 | h3 | h3) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
    have h_eq2 : b ^ 5 % 3 = b % 3 := by 
      rcases h4 with (h4 | h4 | h4) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
    have h_eq3 : c ^ 5 % 3 = c % 3 := by 
      rcases h5 with (h5 | h5 | h5) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h5]
    omega

  have h1'' : (a ^ 5 + b ^ 5 + c ^ 5) % 5 = 0 := by
    have h2 : (a + b + c) % 5 = 0 := by
      omega
    have h3 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by 
      omega
    have h4 : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by 
      omega
    have h5 : c % 5 = 0 ∨ c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by 
      omega
    have h_eq1 : a ^ 5 % 5 = a % 5 := by 
      rcases h3 with (h3 | h3 | h3 | h3 | h3) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
    have h_eq2 : b ^ 5 % 5 = b % 5 := by 
      rcases h4 with (h4 | h4 | h4 | h4 | h4) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
    have h_eq3 : c ^ 5 % 5 = c % 5 := by 
      rcases h5 with (h5 | h5 | h5 | h5 | h5) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h5]
    omega

  omega