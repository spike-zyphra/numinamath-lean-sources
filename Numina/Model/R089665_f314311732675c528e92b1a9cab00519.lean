import Mathlib

theorem number_theory_112061 (a b c : ℤ) : 3 ∣ a + b + c → 3 ∣ a^3 + b^3 + c^3 := by
  intro h
  have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
    omega
  have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by 
    omega
  have h3 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by 
    omega
  rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3) <;> ( 
    simp [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.mul_emod, pow_three, h1, h2, h3, Int.add_emod, Int.mul_emod] at h ⊢
    <;> omega
  )