import Mathlib

theorem number_theory_87205 (a b : ℤ) (h : 11 ∣ a^2 + b^2 + 9 * a * b) : 11 ∣ a^2 - b^2 := by 
  have h1 : a % 11 = 0 ∨ a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by
    omega
  have h2 : b % 11 = 0 ∨ b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := by 
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> ( 
    have h3 : (a ^ 2 + b ^ 2 + 9 * a * b) % 11 = 0 := by 
      omega 
    have h4 : (a ^ 2 - b ^ 2) % 11 = 0 := by 
      simp [Int.add_emod, Int.sub_emod, pow_two, Int.mul_emod, h1, h2] at h3 ⊢ 
      <;> omega 
    exact Int.dvd_of_emod_eq_zero h4 
  )