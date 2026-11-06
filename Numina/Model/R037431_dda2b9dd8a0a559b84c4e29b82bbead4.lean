import Mathlib

theorem number_theory_235108 (a b c d e : ℤ) :
    3 ∣ a + b + c ∨ 3 ∣ a + b + d ∨ 3 ∣ a + b + e ∨
      3 ∣ a + c + d ∨ 3 ∣ a + c + e ∨ 3 ∣ b + c + d ∨
      3 ∣ b + c + e ∨ 3 ∣ d + e + a ∨ 3 ∣ d + e + b ∨
      3 ∣ d + e + c := by
  have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  have h3 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
  have h4 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  have h5 : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
  rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5) <;> simp [Int.dvd_iff_emod_eq_zero, Int.add_emod, h1, h2, h3, h4, h5] <;> omega