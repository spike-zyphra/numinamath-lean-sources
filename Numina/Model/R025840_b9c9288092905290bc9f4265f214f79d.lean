import Mathlib

theorem number_theory_193999 (m n : ℤ) (h : Even (m^2 + n^2)) :
    ¬(∃ k, Odd k ∧ k = m + n) := by 
  by_contra h1
  rcases h1 with ⟨k, hk1, hk2⟩
  have h2 : (m + n) % 2 = 1 := by
    have h3 : Odd k := hk1
    obtain ⟨c, hc⟩ := h3
    have hk4 : k = m + n := by 
      linarith [hk2]
    rw [hk4] at hc
    omega 
  have h3 : m % 2 = 0 ∨ m % 2 = 1 := by 
    omega 
  have h4 : n % 2 = 0 ∨ n % 2 = 1 := by 
    omega 
  have h5 : (m ^ 2 + n ^ 2 : ℤ) % 2 = 0 := by
    have h0 : (m ^ 2 + n ^ 2 : ℤ) % 2 = 0 := by
      have h6 : Even (m^2 + n^2) := h
      obtain ⟨c, hc⟩ := h6
      omega 
    omega 
  have h6 : ((m + n) % 2 = 0) := by
    have h7 : (m ^ 2 + n ^ 2 : ℤ) % 2 = (m + n : ℤ) % 2 := by 
      have h8 : m % 2 = 0 ∨ m % 2 = 1 := by 
        omega 
      have h9 : n % 2 = 0 ∨ n % 2 = 1 := by 
        omega 
      rcases h8 with (h8 | h8)
      · -- m % 2 = 0
        rcases h9 with (h9 | h9)
        · -- n % 2 = 0
          simp [Int.add_emod, pow_two, Int.mul_emod, h8, h9]
        · -- n % 2 = 1
          simp [Int.add_emod, pow_two, Int.mul_emod, h8, h9]
      · -- m % 2 = 1
        rcases h9 with (h9 | h9)
        · -- n % 2 = 0
          simp [Int.add_emod, pow_two, Int.mul_emod, h8, h9]
        · -- n % 2 = 1
          simp [Int.add_emod, pow_two, Int.mul_emod, h8, h9]
    omega 
  omega