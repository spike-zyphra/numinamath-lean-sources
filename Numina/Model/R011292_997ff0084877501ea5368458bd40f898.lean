import Mathlib

theorem number_theory_231290 (n : ℤ) : 77 ∣ n^18 - n^12 - n^8 + n^2 := by
  have h1 : (n ^ 18 - n ^ 12 - n ^ 8 + n ^ 2) % 7 = 0 := by
    have h1 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h1, Int.emod] <;> omega
  have h2 : (n ^ 18 - n ^ 12 - n ^ 8 + n ^ 2) % 11 = 0 := by
    have h2 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h2, Int.emod] <;> omega
  omega