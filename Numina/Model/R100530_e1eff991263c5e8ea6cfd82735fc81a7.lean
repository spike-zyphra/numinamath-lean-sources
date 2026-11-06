import Mathlib

theorem number_theory_72114 :
    IsGreatest {x | ∀ m n : ℤ, Odd m → Odd n → n < m → x ∣ m ^ 2 - n ^ 2} 8 := by
  constructor 
  · -- Show that 8 is in the set
    intro m n h_odd_m h_odd_n h_n_lt_m
    have h1 : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by
      rcases h_odd_m with ⟨k, hk⟩
      omega
    have h2 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
      rcases h_odd_n with ⟨k, hk⟩
      omega
    have h3 : m^2 % 8 = 1 := by
      rcases h1 with (h | h | h | h)
      · norm_num [pow_two, Int.mul_emod, h]
      · norm_num [pow_two, Int.mul_emod, h]
      · norm_num [pow_two, Int.mul_emod, h]
      · norm_num [pow_two, Int.mul_emod, h]
    have h4 : n^2 % 8 = 1 := by
      rcases h2 with (h | h | h | h)
      · norm_num [pow_two, Int.mul_emod, h]
      · norm_num [pow_two, Int.mul_emod, h]
      · norm_num [pow_two, Int.mul_emod, h]
      · norm_num [pow_two, Int.mul_emod, h]
    have h5 : (m^2 - n^2) % 8 = 0 := by
      omega
    exact Int.dvd_of_emod_eq_zero h5
  · -- Show that 8 is greatest
    intro x h_x
    have h1 := h_x 3 1 (by decide) (by decide) (by norm_num)
    have h2 := h_x 5 3 (by decide) (by decide) (by norm_num)
    norm_num at h1 h2
    have h3 : x ≤ 8 := by
      exact Int.le_of_dvd (show (0 : ℤ) < 8 by norm_num) h1
    linarith