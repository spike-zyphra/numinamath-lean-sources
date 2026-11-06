import Mathlib

theorem number_theory_159335 (a b c d : ℤ) :
    12 ∣ (b - a) * (c - a) * (d - a) * (d - c) * (d - b) * (c - b) := by

  have h1 : (b - a) * (c - a) * (d - a) * (d - c) * (d - b) * (c - b) % 3 = 0 := by
    have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    have h3 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
    have h4 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4) <;> simp [Int.mul_emod, Int.sub_emod, h1, h2, h3, h4]
    <;> omega
  have h2 : (b - a) * (c - a) * (d - a) * (d - c) * (d - b) * (c - b) % 4 = 0 := by
    have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
    have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
    have h3 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
    have h4 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4 | h4) <;> simp [Int.mul_emod, Int.sub_emod, h1, h2, h3, h4]
    <;> omega
  omega