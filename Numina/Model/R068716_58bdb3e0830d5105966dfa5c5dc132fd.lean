import Mathlib

theorem number_theory_112469 (a : ℤ) (h : Odd a) : 8 ∣ a^2 - 1 := by
  have h1 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
    rcases h with ⟨k, hk⟩
    omega
  rcases h1 with (h1 | h1 | h1 | h1)
  · -- case a % 8 = 1
    have h2 : a ^ 2 % 8 = 1 := by
      norm_num [pow_two, Int.mul_emod, h1]
    omega
  · -- case a % 8 = 3
    have h2 : a ^ 2 % 8 = 1 := by
      norm_num [pow_two, Int.mul_emod, h1]
    omega
  · -- case a % 8 = 5
    have h2 : a ^ 2 % 8 = 1 := by
      norm_num [pow_two, Int.mul_emod, h1]
    omega
  · -- case a % 8 = 7
    have h2 : a ^ 2 % 8 = 1 := by
      norm_num [pow_two, Int.mul_emod, h1]
    omega