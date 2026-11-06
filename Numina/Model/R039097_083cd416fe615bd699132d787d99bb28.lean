import Mathlib

theorem number_theory_104318 (a b : ℤ) (h : (a + b) * (a * b) = 20182017) :
    False := by
  have h1 : (a + b) * (a * b) % 4 = 1 := by
    omega
  have h2 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by
    omega
  have h3 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
    omega
  rcases h2 with (h2 | h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3 | h3) <;> simp [Int.add_emod, Int.mul_emod, h2, h3] at h1 <;> omega