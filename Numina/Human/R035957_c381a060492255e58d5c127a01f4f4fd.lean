import Mathlib

theorem number_theory_258327 (a b : ℤ) : 6 ∣ a + b ↔ 6 ∣ a^3 + b^3 := by
  constructor
  · intro h
    have h1 : a^3 + b^3 = (a + b) * (a^2 - a * b + b^2) := by ring
    rw [h1]
    exact dvd_mul_of_dvd_left h _
  · intro h
    have h1 : a^3 % 6 = a % 6 := by
      have h1 : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1) <;>
        simp [h1, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h2 : b^3 % 6 = b % 6 := by
      have h2 : b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2) <;>
        simp [h2, pow_three, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h3 : (a + b) % 6 = 0 := by
      omega
    exact Int.dvd_of_emod_eq_zero h3