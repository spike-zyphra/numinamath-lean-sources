import Mathlib

theorem number_theory_199263 : ¬∃ x y z : ℤ, x^2 + y^5 = 11 ∧ z^2 - 2 * y^2 = 1 := by
  rintro ⟨x, y, z, h1, h2⟩
  have h3 : z ^ 2 % 8 = 0 ∨ z ^ 2 % 8 = 1 ∨ z ^ 2 % 8 = 4 := by
    have h1 : z % 8 = 0 ∨ z % 8 = 1 ∨ z % 8 = 2 ∨ z % 8 = 3 ∨ z % 8 = 4 ∨ z % 8 = 5 ∨ z % 8 = 6 ∨ z % 8 = 7 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h | h) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h]

  have h4 : (1 + 2 * y ^ 2) % 8 = 1 ∨ (1 + 2 * y ^ 2) % 8 = 5 ∨ (1 + 2 * y ^ 2) % 8 = 3 := by
    have h5 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by 
      omega
    rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h5]

  have h5 : z ^ 2 % 8 = (1 + 2 * y ^ 2) % 8 := by 
    omega

  have h6 : (1 + 2 * y ^ 2) % 8 = 1 := by
    omega

  have h7 : y % 2 = 0 := by
    by_cases h : y % 2 = 1
    · 
      have h9 : y % 2 = 1 := by
        omega
      have h10 : y ^ 2 % 4 = 1 := by
        have h99 : y % 2 = 1 := h9
        have h10 : y % 4 = 1 ∨ y % 4 = 3 := by
          omega
        rcases h10 with (h10 | h10)
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h10] 
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h10] 
      omega
    omega

  have h8' : y ^ 5 % 32 = 0 := by
    have h9 : y % 2 = 0 := h7
    have h10 : ∃ k : ℤ, y = 2 * k := by 
      refine' ⟨y / 2, by omega⟩
    rcases h10 with ⟨k, hk⟩
    rw [hk]
    ring_nf
    all_goals
      omega

  have h13 : x ^ 2 % 32 = 11 := by 
    omega

  have h14 : x ^ 2 % 32 = 0 ∨ x ^ 2 % 32 = 1 ∨ x ^ 2 % 32 = 4 ∨ x ^ 2 % 32 = 9 ∨ x ^ 2 % 32 = 16 ∨ x ^ 2 % 32 = 17 ∨ x ^ 2 % 32 = 25 := by 
    have h100 : x % 32 = 0 ∨ x % 32 = 1 ∨ x % 32 = 2 ∨ x % 32 = 3 ∨ x % 32 = 4 ∨ x % 32 = 5 ∨ x % 32 = 6 ∨ x % 32 = 7 ∨ x % 32 = 8 ∨ x % 32 = 9 ∨ x % 32 = 10 ∨ x % 32 = 11 ∨ x % 32 = 12 ∨ x % 32 = 13 ∨ x % 32 = 14 ∨ x % 32 = 15 ∨ x % 32 = 16 ∨ x % 32 = 17 ∨ x % 32 = 18 ∨ x % 32 = 19 ∨ x % 32 = 20 ∨ x % 32 = 21 ∨ x % 32 = 22 ∨ x % 32 = 23 ∨ x % 32 = 24 ∨ x % 32 = 25 ∨ x % 32 = 26 ∨ x % 32 = 27 ∨ x % 32 = 28 ∨ x % 32 = 29 ∨ x % 32 = 30 ∨ x % 32 = 31 := by 
      omega
    rcases h100 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h] 
  omega