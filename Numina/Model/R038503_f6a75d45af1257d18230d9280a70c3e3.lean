import Mathlib

theorem number_theory_119990 (a b : ℤ) (h : 24*a^2+1=b^2) :
    (5 ∣ a ∧ ¬5 ∣ b) ∨ (¬5 ∣ a ∧ 5 ∣ b) := by

  by_cases h5a : 5 ∣ a

  · -- Assume 5 divides a
    have h6 : a % 5 = 0 := by 
      omega
    have ha2 : a^2 % 5 = 0 := by
      simp [pow_two, Int.mul_emod, h6]
    have hb2 : b^2 % 5 = 1 := by
      omega
    have h5b : ¬5 ∣ b := by
      by_contra h1
      have h11 : b % 5 = 0 := by
        omega
      have : b^2 % 5 = 0 := by
        simp [pow_two, Int.mul_emod, h11]
      omega
    left
    exact ⟨h5a, h5b⟩

  · -- Assume 5 does not divide a
    have h5b : 5 ∣ b := by 
      by_contra h
      push_neg at h 
      have h6 : ¬5 ∣ b := by 
        simpa using h 
      have h7 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by 
        omega 
      have h8 : b^2 % 5 = 1 ∨ b^2 % 5 = 4 := by
        rcases h7 with (h7 | h7 | h7 | h7) <;> norm_num [pow_two, Int.mul_emod, h7]
      have h9 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by 
        omega 
      have h10 : a^2 % 5 = 1 ∨ a^2 % 5 = 4 := by
        rcases h9 with (h9 | h9 | h9 | h9) <;> norm_num [pow_two, Int.mul_emod, h9]
      have h11 : (24 * a^2 + 1) % 5 = b^2 % 5 := by 
        omega 
      omega 
    have h7 : ¬5 ∣ a := by 
      omega 
    right 
    exact ⟨h7, h5b⟩