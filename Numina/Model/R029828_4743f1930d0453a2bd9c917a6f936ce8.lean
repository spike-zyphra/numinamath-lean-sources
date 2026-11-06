import Mathlib

theorem number_theory_92628 (a b c : ℤ) : 7 ∣ a^4 + b^4 + c^4 → 7 ∣ a^2 + b^2 + c^2 := by
  intro h
  have h1 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by omega
  have h2 : b % 7 = 0 ∨ b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by omega
  have h3 : c % 7 = 0 ∨ c % 7 = 1 ∨ c % 7 = 2 ∨ c % 7 = 3 ∨ c % 7 = 4 ∨ c % 7 = 5 ∨ c % 7 = 6 := by omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> ( 
    simp [Int.dvd_iff_emod_eq_zero, pow_succ, Int.add_emod, Int.mul_emod, h1, h2, h3] at h ⊢
    <;> omega 
  )