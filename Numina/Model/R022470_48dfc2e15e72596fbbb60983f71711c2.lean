import Mathlib

theorem number_theory_172016 (a b c d : ℤ) (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
    12 ∣ (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) := by
  rcases h with ⟨ha1, ha2, ha3, hb1, hb2, hc⟩
  have h1 : (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) % 3 = 0 := by
    have h2 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
      omega
    have h3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by 
      omega
    have h4 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by 
      omega
    have h5 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by 
      omega
    have h6 : a % 3 = b % 3 ∨ a % 3 = c % 3 ∨ a % 3 = d % 3 ∨ b % 3 = c % 3 ∨ b % 3 = d % 3 ∨ c % 3 = d % 3 := by 
      omega
    rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6)
    · -- a ≡ b (mod 3)
      have h7 : (a - b) % 3 = 0 := by 
        omega
      simp [Int.mul_emod, h7]
    · -- a ≡ c (mod 3)
      have h7 : (a - c) % 3 = 0 := by 
        omega
      simp [Int.mul_emod, h7]
    · -- a ≡ d (mod 3)
      have h7 : (a - d) % 3 = 0 := by 
        omega
      simp [Int.mul_emod, h7]
    · -- b ≡ c (mod 3)
      have h7 : (b - c) % 3 = 0 := by 
        omega
      simp [Int.mul_emod, h7]
    · -- b ≡ d (mod 3)
      have h7 : (b - d) % 3 = 0 := by 
        omega
      simp [Int.mul_emod, h7]
    · -- c ≡ d (mod 3)
      have h7 : (c - d) % 3 = 0 := by 
        omega
      simp [Int.mul_emod, h7]

  have h2 : (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) % 4 = 0 := by
    have h2 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by
      omega
    have h3 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
      omega
    have h4 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by
      omega
    have h5 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5 | h5) <;> simp [Int.add_emod, Int.mul_emod, Int.sub_emod, h2, h3, h4, h5, Int.mul_emod]

  omega