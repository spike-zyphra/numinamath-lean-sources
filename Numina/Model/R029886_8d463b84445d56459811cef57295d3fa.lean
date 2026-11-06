import Mathlib

theorem number_theory_106576 (a b c : ℤ) (h : 6 ∣ a + b + c) : 6 ∣ a^5 + b^3 + c := by
  have h1 : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by
    omega
  have h2 : b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by
    omega
  have h3 : a ^ 5 % 6 = a % 6 := by
    rcases h1 with (h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    <;> omega
  have h4 : b ^ 3 % 6 = b % 6 := by
    rcases h2 with (h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    <;> omega
  have h5 : (a ^ 5 + b ^ 3 + c) % 6 = 0 := by
    have h6 : (a ^ 5 % 6) = (a % 6) := h3
    have h7 : (b ^ 3 % 6) = (b % 6) := h4
    have h8 : (a + b + c) % 6 = 0 := by
      omega
    omega
  exact Int.dvd_of_emod_eq_zero h5