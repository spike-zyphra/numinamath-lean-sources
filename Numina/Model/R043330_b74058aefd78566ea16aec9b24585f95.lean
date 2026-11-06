import Mathlib

theorem number_theory_44855 (m n : ℤ) : 9 ∣ m^2 + m * n + n^2 → 3 ∣ m ∧ 3 ∣ n := by
  intro h
  have h1 : m % 9 = 0 ∨ m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 3 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 7 ∨ m % 9 = 8 := by 
    omega 
  have h2 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
    omega 
  have h3 : (m^2 + m * n + n^2) % 9 = 0 := by 
    omega 
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h1, h2] at h3 
    <;> omega