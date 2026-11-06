import Mathlib

theorem number_theory_191600 (a : ℤ) (h : ¬ 5 ∣ a) : 5 ∣ a^4 - 1 := by
  have h1 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by 
    omega
  rcases h1 with (h1 | h1 | h1 | h1)
  · -- a % 5 = 1
    have h2 : a^4 % 5 = 1 := by
      have h3 : a % 5 = 1 := h1
      norm_num [pow_succ, Int.mul_emod, h3] at *
    have h3 : (a^4 - 1) % 5 = 0 := by
      omega
    exact Int.dvd_of_emod_eq_zero h3
  · -- a % 5 = 2
    have h2 : a^4 % 5 = 1 := by
      have h3 : a % 5 = 2 := h1
      norm_num [pow_succ, Int.mul_emod, h3] at *
    have h3 : (a^4 - 1) % 5 = 0 := by 
      omega
    exact Int.dvd_of_emod_eq_zero h3
  · -- a % 5 = 3
    have h2 : a^4 % 5 = 1 := by
      have h3 : a % 5 = 3 := h1
      norm_num [pow_succ, Int.mul_emod, h3] at *
    have h3 : (a^4 - 1) % 5 = 0 := by 
      omega
    exact Int.dvd_of_emod_eq_zero h3
  · -- a % 5 = 4
    have h2 : a^4 % 5 = 1 := by
      have h3 : a % 5 = 4 := h1
      norm_num [pow_succ, Int.mul_emod, h3] at *
    have h3 : (a^4 - 1) % 5 = 0 := by 
      omega
    exact Int.dvd_of_emod_eq_zero h3