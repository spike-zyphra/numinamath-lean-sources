import Mathlib

theorem number_theory_298041 (a b c : ℤ) (h : a > 0) (h' : b > 0) (h'' : c > 0)
    (h''' : a^2 + b^2 = c^2) :
    30 ∣ a * b * c := by 
  have h1 : a * b * c % 2 = 0 := by 
    have h2 : a % 2 = 0 ∨ b % 2 = 0 ∨ c % 2 = 0 := by 
      by_contra h
      push_neg at h
      have h1 : a % 2 = 1 := by omega
      have h2 : b % 2 = 1 := by omega
      have h3 : c % 2 = 1 := by omega
      have h4 : a^2 % 4 = 1 := by 
        have h5 : a % 4 = 1 ∨ a % 4 = 3 := by omega
        rcases h5 with (h5 | h5)
        · simp [pow_two, Int.add_emod, Int.mul_emod, h5]
        · simp [pow_two, Int.add_emod, Int.mul_emod, h5]
      have h5 : b^2 % 4 = 1 := by 
        have h6 : b % 4 = 1 ∨ b % 4 = 3 := by omega
        rcases h6 with (h6 | h6)
        · simp [pow_two, Int.add_emod, Int.mul_emod, h6]
        · simp [pow_two, Int.add_emod, Int.mul_emod, h6]
      have h6 : c^2 % 4 = 1 := by 
        have h7 : c % 4 = 1 ∨ c % 4 = 3 := by omega
        rcases h7 with (h7 | h7)
        · simp [pow_two, Int.add_emod, Int.mul_emod, h7]
        · simp [pow_two, Int.add_emod, Int.mul_emod, h7]
      have h7 : (a^2 + b^2) % 4 = 2 := by 
        omega
      have h8 : (a^2 + b^2) % 4 = c^2 % 4 := by 
        omega
      omega
    rcases h2 with (h2 | h2 | h2)
    · simp [Int.mul_emod, h2]
    · simp [Int.mul_emod, h2]
    · simp [Int.mul_emod, h2]
  have h2 : a * b * c % 3 = 0 := by 
    have h3 : a % 3 = 0 ∨ b % 3 = 0 ∨ c % 3 = 0 := by 
      by_contra h
      push_neg at h
      have h1 : a % 3 = 1 ∨ a % 3 = 2 := by omega
      have h2 : b % 3 = 1 ∨ b % 3 = 2 := by omega
      have h3 : c % 3 = 1 ∨ c % 3 = 2 := by omega
      have h4 : a^2 % 3 = 1 := by 
        rcases h1 with (h1 | h1)
        · simp [pow_two, Int.add_emod, Int.mul_emod, h1]
        · simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h5 : b^2 % 3 = 1 := by 
        rcases h2 with (h2 | h2)
        · simp [pow_two, Int.add_emod, Int.mul_emod, h2]
        · simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      have h6 : c^2 % 3 = 1 := by 
        rcases h3 with (h3 | h3)
        · simp [pow_two, Int.add_emod, Int.mul_emod, h3]
        · simp [pow_two, Int.add_emod, Int.mul_emod, h3]
      have h7 : (a^2 + b^2) % 3 = 2 := by 
        omega
      have h8 : (a^2 + b^2) % 3 = c^2 % 3 := by 
        omega
      omega
    rcases h3 with (h3 | h3 | h3)
    · simp [Int.mul_emod, h3]
    · simp [Int.mul_emod, h3]
    · simp [Int.mul_emod, h3]
  have h3 : a * b * c % 5 = 0 := by 
    have h5 : a % 5 = 0 ∨ b % 5 = 0 ∨ c % 5 = 0 := by 
      by_contra h
      push_neg at h
      have h1 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
      have h2 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
      have h3 : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by omega
      have h4 : a^2 % 5 = 1 ∨ a^2 % 5 = 4 := by 
        rcases h1 with (h1 | h1 | h1 | h1) <;> (simp [pow_two, Int.add_emod, Int.mul_emod, h1] <;> omega)
      have h5 : b^2 % 5 = 1 ∨ b^2 % 5 = 4 := by 
        rcases h2 with (h2 | h2 | h2 | h2) <;> (simp [pow_two, Int.add_emod, Int.mul_emod, h2] <;> omega)
      have h6 : c^2 % 5 = 1 ∨ c^2 % 5 = 4 := by 
        rcases h3 with (h3 | h3 | h3 | h3) <;> (simp [pow_two, Int.add_emod, Int.mul_emod, h3] <;> omega)
      have h7 : (a^2 + b^2) % 5 = 2 ∨ (a^2 + b^2) % 5 = 0 ∨ (a^2 + b^2) % 5 = 3 := by 
        rcases h4 with (h4 | h4) <;> rcases h5 with (h5 | h5) <;> (simp [Int.add_emod, h4, h5] <;> omega)
      have h8 : (a^2 + b^2) % 5 = c^2 % 5 := by 
        omega
      rcases h7 with (h7 | h7 | h7)
      · -- Case (a^2 + b^2) % 5 = 2
        have h9 : c^2 % 5 = 2 := by omega
        omega
      · -- Case (a^2 + b^2) % 5 = 0
        have h9 : c^2 % 5 = 0 := by omega
        omega
      · -- Case (a^2 + b^2) % 5 = 3
        have h9 : c^2 % 5 = 3 := by omega
        omega
    rcases h5 with (h5 | h5 | h5)
    · simp [Int.mul_emod, h5]
    · simp [Int.mul_emod, h5]
    · simp [Int.mul_emod, h5]
  -- Given that a * b * c is divisible by 2, 3, and 5, it is divisible by 30
  omega