import Mathlib

theorem number_theory_259336 (a b c : ℤ) (h : 18 ∣ a^3 + b^3 + c^3) : 6 ∣ a * b * c := by
  have h1 : (a^3 + b^3 + c^3) % 2 = 0 := by
    omega
  have h2 : (a^3 + b^3 + c^3) % 9 = 0 := by
    omega
  have h3 : a % 2 = 0 ∨ b % 2 = 0 ∨ c % 2 = 0 := by
    have h3 : (a^3 + b^3 + c^3) % 2 = 0 := h1
    have h4 : a^3 % 2 = a % 2 := by
      have h11 : a % 2 = 0 ∨ a % 2 = 1 := by 
        omega
      rcases h11 with (h11 | h11)
      · simp [h11, pow_succ, Int.add_emod, Int.mul_emod]
      · simp [h11, pow_succ, Int.add_emod, Int.mul_emod]
    have h5 : b^3 % 2 = b % 2 := by
      have h11 : b % 2 = 0 ∨ b % 2 = 1 := by 
        omega
      rcases h11 with (h11 | h11)
      · simp [h11, pow_succ, Int.add_emod, Int.mul_emod]
      · simp [h11, pow_succ, Int.add_emod, Int.mul_emod]
    have h6 : c^3 % 2 = c % 2 := by
      have h11 : c % 2 = 0 ∨ c % 2 = 1 := by 
        omega
      rcases h11 with (h11 | h11)
      · simp [h11, pow_succ, Int.add_emod, Int.mul_emod]
      · simp [h11, pow_succ, Int.add_emod, Int.mul_emod]
    have h7 : (a^3 + b^3 + c^3) % 2 = (a + b + c) % 2 := by
      simp [Int.add_emod, Int.mul_emod, h4, h5, h6]
    rw [h7] at h3
    omega
  have h4 : a % 3 = 0 ∨ b % 3 = 0 ∨ c % 3 = 0 := by
    by_contra h4
    push_neg at h4
    have h5 : a % 3 = 1 ∨ a % 3 = 2 := by 
      omega
    have h6 : b % 3 = 1 ∨ b % 3 = 2 := by 
      omega
    have h7 : c % 3 = 1 ∨ c % 3 = 2 := by 
      omega
    have h8 : a^3 % 9 = 1 ∨ a^3 % 9 = 8 := by
      have h10 : a % 3 = 1 ∨ a % 3 = 2 := h5
      have h11 : a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨ a % 9 = 7 ∨ a % 9 = 8 := by
        omega
      rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11) <;> simp [h11, pow_succ, Int.add_emod, Int.mul_emod]
    have h9 : b^3 % 9 = 1 ∨ b^3 % 9 = 8 := by
      have h10 : b % 3 = 1 ∨ b % 3 = 2 := h6
      have h11 : b % 9 = 1 ∨ b % 9 = 2 ∨ b % 9 = 4 ∨ b % 9 = 5 ∨ b % 9 = 7 ∨ b % 9 = 8 := by
        omega
      rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11) <;> simp [h11, pow_succ, Int.add_emod, Int.mul_emod]
    have h10 : c^3 % 9 = 1 ∨ c^3 % 9 = 8 := by
      have h10 : c % 3 = 1 ∨ c % 3 = 2 := h7
      have h11 : c % 9 = 1 ∨ c % 9 = 2 ∨ c % 9 = 4 ∨ c % 9 = 5 ∨ c % 9 = 7 ∨ c % 9 = 8 := by
        omega
      rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11) <;> simp [h11, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  have h5 : (a * b * c) % 2 = 0 := by
    rcases h3 with (h3 | h3 | h3)
    · simp [Int.mul_emod, h3]
    · simp [Int.mul_emod, h3]
    · simp [Int.mul_emod, h3]
  have h6 : (a * b * c) % 3 = 0 := by
    rcases h4 with (h4 | h4 | h4)
    · simp [Int.mul_emod, h4]
    · simp [Int.mul_emod, h4]
    · simp [Int.mul_emod, h4]
  omega