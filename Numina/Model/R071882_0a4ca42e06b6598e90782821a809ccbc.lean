import Mathlib

theorem algebra_68796 {a b : ℤ} (ha : Odd (2 * a + 1)) (hb : Odd (2 * b + 1)) (h : a > b) :
    8 ∣ (2 * a + 1)^2 - (2 * b + 1)^2 := by

  have h3 : (2 * a + 1) % 8 = 1 ∨ (2 * a + 1) % 8 = 3 ∨ (2 * a + 1) % 8 = 5 ∨ (2 * a + 1) % 8 = 7 := by
    omega

  have h4 : (2 * b + 1) % 8 = 1 ∨ (2 * b + 1) % 8 = 3 ∨ (2 * b + 1) % 8 = 5 ∨ (2 * b + 1) % 8 = 7 := by
    omega
  
  have h5 : ((2 * a + 1)^2) % 8 = 1 := by
    rcases h3 with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h] at *

  have h6 : ((2 * b + 1)^2) % 8 = 1 := by
    rcases h4 with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h] at *
  
  have h7 : ((2 * a + 1)^2 - (2 * b + 1)^2) % 8 = 0 := by
    omega
  
  exact Int.dvd_of_emod_eq_zero h7