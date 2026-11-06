import Mathlib

theorem number_theory_7118 {n a b : ℤ} (hn : Even n) (h : n = a^2 - b^2) :
    4 ∣ n := by
  have h5 : n % 2 = 0 := by
    obtain ⟨k, hk⟩ := hn
    omega

  have h8 : a^2 % 2 = b^2 % 2 := by 
    omega

  have h9 : a % 2 = b % 2 := by
    by_cases h1 : a % 2 = 0
    · -- Suppose a is even
      by_cases h2 : b % 2 = 0
      · -- If b is even, then both are even
        omega
      · -- If b is odd
        have h3 : b % 2 = 1 := by omega
        have h4 : a^2 % 2 = 0 := by
          simp [h1, pow_two, Int.mul_emod]
        have h5 : b^2 % 2 = 1 := by
          simp [h3, pow_two, Int.mul_emod]
        omega -- this contradicts h8
    · -- If a is odd
      have h1 : a % 2 = 1 := by omega
      by_cases h2 : b % 2 = 0
      · -- If b is even
        have h3 : b % 2 = 0 := by omega
        have h4 : a^2 % 2 = 1 := by
          simp [h1, pow_two, Int.mul_emod]
        have h5 : b^2 % 2 = 0 := by
          simp [h3, pow_two, Int.mul_emod]
        omega -- this contradicts h8
      · -- If b is odd
        have h2 : b % 2 = 1 := by omega
        omega 
  by_cases h10 : a % 2 = 0
  · -- If a is even, then b must be even
    have h11 : b % 2 = 0 := by 
      omega 
    have h12 : a % 4 = 0 ∨ a % 4 = 2 := by
      omega
    have h13 : b % 4 = 0 ∨ b % 4 = 2 := by
      omega
    have h14 : a^2 % 4 = 0 := by
      rcases h12 with (h12 | h12) <;> simp [h12, pow_two, Int.add_emod, Int.mul_emod]
    have h15 : b^2 % 4 = 0 := by
      rcases h13 with (h13 | h13) <;> simp [h13, pow_two, Int.add_emod, Int.mul_emod]
    omega
  · -- If a is odd, then b must be odd
    have h11 : b % 2 = 1 := by 
      omega 
    have h12 : a % 4 = 1 ∨ a % 4 = 3 := by
      omega
    have h13 : b % 4 = 1 ∨ b % 4 = 3 := by
      omega
    have h14 : a^2 % 4 = 1 := by
      rcases h12 with (h12 | h12) <;> simp [h12, pow_two, Int.add_emod, Int.mul_emod]
    have h15 : b^2 % 4 = 1 := by
      rcases h13 with (h13 | h13) <;> simp [h13, pow_two, Int.add_emod, Int.mul_emod]
    omega