import Mathlib

theorem number_theory_193487 {a b c : ℤ} (h : 7 ∣ a^3 + b^3 + c^3) : 7 ∣ a * b * c := by
  by_contra h1
  push_neg at h1
  have h2 : a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
    by_contra h2
    push_neg at h2
    have : a % 7 = 0 := by 
      omega
    have h3 : a * b * c % 7 = 0 := by
      simp [Int.mul_emod, this]
    omega
  have h3 : b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by
    by_contra h3
    push_neg at h3
    have : b % 7 = 0 := by 
      omega
    have h4 : a * b * c % 7 = 0 := by
      simp [Int.mul_emod, this]
    omega
  have h4 : c % 7 = 1 ∨ c % 7 = 2 ∨ c % 7 = 3 ∨ c % 7 = 4 ∨ c % 7 = 5 ∨ c % 7 = 6 := by
    by_contra h4
    push_neg at h4
    have : c % 7 = 0 := by 
      omega
    have h5 : a * b * c % 7 = 0 := by
      simp [Int.mul_emod, this]
    omega
  have h5 : a^3 % 7 = 1 ∨ a^3 % 7 = 6 := by
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h2]
  have h6 : b^3 % 7 = 1 ∨ b^3 % 7 = 6 := by
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
  have h7 : c^3 % 7 = 1 ∨ c^3 % 7 = 6 := by
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h4]
  omega