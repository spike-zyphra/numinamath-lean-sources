import Mathlib

theorem number_theory_223375 : ∀ m n : ℤ, ¬ 9 ∣ m^2 + n^2 + m + n - 1 := by
  intro m n
  have h1 : m % 9 = 0 ∨ m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 3 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 7 ∨ m % 9 = 8 := by 
    omega
  have h2 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> norm_num [Int.dvd_iff_emod_eq_zero, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h1, h2, Int.emod] <;> omega