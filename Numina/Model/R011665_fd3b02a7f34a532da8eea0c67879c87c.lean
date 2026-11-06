import Mathlib

theorem number_theory_268228 : ¬∃ x y : ℤ, 19 * x ^ 3 - 17 * y ^ 3 = 50 := by
  rintro ⟨x, y, h_eq⟩
  have h1 : (19 * x ^ 3 - 17 * y ^ 3) % 9 = 50 % 9 := by
    omega
  have h2 : (19 * x ^ 3 - 17 * y ^ 3) % 9 = (x ^ 3 + y ^ 3) % 9 := by
    have h3 : (19 * x ^ 3) % 9 = (x ^ 3) % 9 := by
      have h4 : (19 : ℤ) % 9 = 1 := by norm_num
      simp [Int.mul_emod, h4]
    have h6 : (-17 * y ^ 3) % 9 = (y ^ 3) % 9 := by
      have h5 : (-17 : ℤ) % 9 = 1 := by norm_num
      have h7 : (-17 * y ^ 3 : ℤ) % 9 = (y ^ 3) % 9 := by
        have h8 : (-17 : ℤ) % 9 = 1 := by norm_num
        have h9 : (-17 : ℤ) % 9 = 1 := by assumption
        have h10 : (-17 : ℤ) = (9 * (-2) + 1 : ℤ) := by omega
        rw [h10]
        simp [Int.add_emod, Int.mul_emod, h9]
        <;> ring_nf
        <;> omega
      assumption
    omega
  have h50 : (50 : ℤ) % 9 = 5 := by norm_num
  have h3 : (x ^ 3 + y ^ 3) % 9 = 5 := by
    omega
  have h4 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by 
    omega
  have h5 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by 
    omega
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> 
  rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;> 
  norm_num [Int.add_emod, pow_succ, Int.mul_emod, h4, h5] at h3
  <;> omega