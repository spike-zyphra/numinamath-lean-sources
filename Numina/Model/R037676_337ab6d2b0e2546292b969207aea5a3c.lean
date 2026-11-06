import Mathlib

theorem number_theory_29852 (m n : ℤ) (hm : 0 < m) (hn : 0 < n) (hmn : Odd (m - n)) :
    ¬ ∃ x : ℤ, x ^ 2 = (m + 3 * n) * (5 * m + 7 * n) := by
  by_contra h
  rcases h with ⟨x, hx⟩
  have h1 : (m - n : ℤ) % 2 = 1 := by 
    obtain ⟨k, hk⟩ := hmn
    omega
  have h2 : (m + 3 * n) * (5 * m + 7 * n) % 8 = 5 := by
    have h3 : (m - n : ℤ) % 2 = 1 := h1
    have h4 : m % 2 ≠ n % 2 := by
      omega
    have h5 : (m + 3 * n) * (5 * m + 7 * n) % 8 = 5 := by
      have h6 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by
        omega
      have h7 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
        omega
      rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6) <;> rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7) <;> 
        simp [Int.add_emod, Int.mul_emod, Int.sub_emod, h6, h7] <;> omega
    exact h5
  have h3 : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
    have h4 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
      omega
    rcases h4 with (h | h | h | h | h | h | h | h) <;> norm_num [h, pow_two, Int.add_emod, Int.mul_emod]
  have h4 : x ^ 2 % 8 = (m + 3 * n) * (5 * m + 7 * n) % 8 := by
    omega
  omega