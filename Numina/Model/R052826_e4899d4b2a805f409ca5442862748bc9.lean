import Mathlib

theorem number_theory_6899 : ∀ a : ℤ, Odd a → 8 ∣ (a^2 - 1) := by
  intro a ha
  rcases ha with ⟨k, hk⟩
  have h1 : a = 2 * k + 1 := by
    linarith
  rw [h1]
  have h2 : (2 * k + 1 : ℤ) ^ 2 % 8 = 1 := by
    have h : (2 * k + 1 : ℤ) % 8 = 1 ∨ (2 * k + 1 : ℤ) % 8 = 3 ∨ (2 * k + 1 : ℤ) % 8 = 5 ∨ (2 * k + 1 : ℤ) % 8 = 7 := by
      omega
    rcases h with (h | h | h | h)
    · norm_num [Int.add_emod, Int.mul_emod, pow_two, h]
    · norm_num [Int.add_emod, Int.mul_emod, pow_two, h]
    · norm_num [Int.add_emod, Int.mul_emod, pow_two, h]
    · norm_num [Int.add_emod, Int.mul_emod, pow_two, h]
  have h3 : ((2 * k + 1 : ℤ)^2 - 1) % 8 = 0 := by
    omega
  exact Int.dvd_of_emod_eq_zero h3