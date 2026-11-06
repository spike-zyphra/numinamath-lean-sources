import Mathlib

theorem number_theory_204335 (n : ℤ) : 120 ∣ n^6 + 2*n^5 - n^2 - 2*n := by
  have h1 : (n ^ 6 + 2 * n ^ 5 - n ^ 2 - 2 * n) % 8 = 0 := by
    have h1 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [Int.add_emod, Int.sub_emod, h1, pow_two, pow_succ, Int.mul_emod]
  have h2 : (n ^ 6 + 2 * n ^ 5 - n ^ 2 - 2 * n) % 3 = 0 := by
    have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2) <;> simp [Int.add_emod, Int.sub_emod, h2, pow_two, pow_succ, Int.mul_emod]
  have h3 : (n ^ 6 + 2 * n ^ 5 - n ^ 2 - 2 * n) % 5 = 0 := by
    have h3 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3) <;> simp [Int.add_emod, Int.sub_emod, h3, pow_two, pow_succ, Int.mul_emod]
  omega