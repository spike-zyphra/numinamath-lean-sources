import Mathlib

theorem number_theory_276212 (n : ℤ) (h : n > 3) :
    5040 ∣ n^7 - 14 * n^5 + 49 * n^3 - 36 * n := by
  have h1 : (n ^ 7 - 14 * n ^ 5 + 49 * n ^ 3 - 36 * n) % 16 = 0 := by
    have h2 : n % 16 = 0 ∨ n % 16 = 1 ∨ n % 16 = 2 ∨ n % 16 = 3 ∨ n % 16 = 4 ∨ n % 16 = 5 ∨ n % 16 = 6 ∨ n % 16 = 7 ∨ n % 16 = 8 ∨ n % 16 = 9 ∨ n % 16 = 10 ∨ n % 16 = 11 ∨ n % 16 = 12 ∨ n % 16 = 13 ∨ n % 16 = 14 ∨ n % 16 = 15 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
  have h2 : (n ^ 7 - 14 * n ^ 5 + 49 * n ^ 3 - 36 * n) % 9 = 0 := by
    have h3 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
  have h3 : (n ^ 7 - 14 * n ^ 5 + 49 * n ^ 3 - 36 * n) % 5 = 0 := by
    have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4) <;> simp [h4, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
  have h4 : (n ^ 7 - 14 * n ^ 5 + 49 * n ^ 3 - 36 * n) % 7 = 0 := by
    have h5 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by 
      omega
    rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5) <;> simp [h5, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod]
  omega