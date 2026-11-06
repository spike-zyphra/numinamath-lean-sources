import Mathlib

theorem number_theory_173445 (a b c d : ℤ) (h : a ≠ b) (h1 : a ≠ c) (h2 : a ≠ d)
    (h3 : b ≠ c) (h4 : b ≠ d) (h5 : c ≠ d) :
    12 ∣ (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) := by
  have h6 : (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) % 3 = 0 := by
    have h_mod_3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    have h1_mod_3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    have h2_mod_3 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
    have h3_mod_3 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases h_mod_3 with (h_a | h_a | h_a) <;> rcases h1_mod_3 with (h_b | h_b | h_b) <;> rcases h2_mod_3 with (h_c | h_c | h_c) <;> rcases h3_mod_3 with (h_d | h_d | h_d) <;> simp [Int.mul_emod, Int.add_emod, Int.sub_emod, h_a, h_b, h_c, h_d] <;> omega
  have h7 : (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) % 4 = 0 := by
    have h_mod_4 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
    have h1_mod_4 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
    have h2_mod_4 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
    have h3_mod_4 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
    rcases h_mod_4 with (h_a | h_a | h_a | h_a) <;> rcases h1_mod_4 with (h_b | h_b | h_b | h_b) <;> rcases h2_mod_4 with (h_c | h_c | h_c | h_c) <;> rcases h3_mod_4 with (h_d | h_d | h_d | h_d) <;> simp [Int.mul_emod, Int.add_emod, Int.sub_emod, h_a, h_b, h_c, h_d] <;> omega
  omega