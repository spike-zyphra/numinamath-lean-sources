import Mathlib

theorem number_theory_283629
    (a b : ℤ)
    (h₀ : Odd a)
    (h₁ : Odd b) :
    8 ∣ (a^2 - b^2) := by
  have h2 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
    rcases h₀ with ⟨k, hk⟩
    omega
  have h3 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by
    rcases h₁ with ⟨k, hk⟩
    omega
  have h4 : a^2 % 8 = 1 := by
    rcases h2 with (h | h | h | h)
    · -- a % 8 = 1
      norm_num [pow_two, Int.mul_emod, h]
    · -- a % 8 = 3
      norm_num [pow_two, Int.mul_emod, h]
    · -- a % 8 = 5
      norm_num [pow_two, Int.mul_emod, h]
    · -- a % 8 = 7
      norm_num [pow_two, Int.mul_emod, h]
  have h5 : b^2 % 8 = 1 := by
    rcases h3 with (h | h | h | h)
    · -- b % 8 = 1
      norm_num [pow_two, Int.mul_emod, h]
    · -- b % 8 = 3
      norm_num [pow_two, Int.mul_emod, h]
    · -- b % 8 = 5
      norm_num [pow_two, Int.mul_emod, h]
    · -- b % 8 = 7
      norm_num [pow_two, Int.mul_emod, h]
  have h6 : (a^2 - b^2) % 8 = 0 := by
    omega
  exact Int.dvd_of_emod_eq_zero h6