import Mathlib

theorem number_theory_112077 (a b c : ℤ) (h : a^2 + b^2 = c^2) :
    3 ∣ a ∨ 3 ∣ b := by
  by_contra h1
  push_neg at h1
  
  have h2 : a % 3 = 1 ∨ a % 3 = 2 := by
    omega

  have h3 : b % 3 = 1 ∨ b % 3 = 2 := by
    omega
  
  have h4 : (a^2) % 3 = 1 := by
    rcases h2 with (h2 | h2)
    · -- case a % 3 = 1
      norm_num [Int.pow_succ, Int.mul_emod, h2]
    · -- case a % 3 = 2
      norm_num [Int.pow_succ, Int.mul_emod, h2]

  have h5 : (b^2) % 3 = 1 := by 
    rcases h3 with (h3 | h3)
    · -- case b % 3 = 1
      norm_num [Int.pow_succ, Int.mul_emod, h3]
    · -- case b % 3 = 2
      norm_num [Int.pow_succ, Int.mul_emod, h3]

  have h6 : (a^2 + b^2) % 3 = 2 := by
    simp [Int.add_emod, h4, h5]

  have h7 : (c^2) % 3 = 0 ∨ (c^2) % 3 = 1 := by
    have h8 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by
      omega
    rcases h8 with (h8 | h8 | h8)
    · -- case c % 3 = 0
      simp [Int.pow_succ, Int.mul_emod, h8]
    · -- case c % 3 = 1
      simp [Int.pow_succ, Int.mul_emod, h8]
    · -- case c % 3 = 2
      simp [Int.pow_succ, Int.mul_emod, h8]

  have h8 : (a^2 + b^2) % 3 = c^2 % 3 := by
    omega

  rw [h8] at h6
  omega