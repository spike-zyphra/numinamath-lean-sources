import Mathlib

theorem number_theory_14582 :
    IsGreatest {k | ∀ m n : ℤ, Odd m → Odd n → n < m → k ∣ m ^ 2 - n ^ 2} 8 := by
  constructor
  · -- Show that 8 is in the set
    show ∀ m n : ℤ, Odd m → Odd n → n < m → (8 : ℤ) ∣ m ^ 2 - n ^ 2
    intro m n h_odd_m h_odd_n h_n_lt_m
    have h1 : m % 2 = 1 := by
      rcases h_odd_m with ⟨k, hk⟩
      omega
    have h2 : n % 2 = 1 := by
      rcases h_odd_n with ⟨k, hk⟩
      omega
    have h3 : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by
      omega
    have h4 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
      omega
    have h5 : m ^ 2 % 8 = 1 := by
      rcases h3 with (h | h | h | h) <;> norm_num [h, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod]
    have h6 : n ^ 2 % 8 = 1 := by
      rcases h4 with (h | h | h | h) <;> norm_num [h, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod]
    have h7 : (m ^ 2 - n ^ 2) % 8 = 0 := by
      omega
    exact Int.dvd_of_emod_eq_zero h7
  · -- Show that no integer greater than 8 is in the set
    intro k hk
    have h1 : k ∣ 3 ^ 2 - 1 ^ 2 := hk 3 1 (by decide) (by decide) (by norm_num)
    have h8 : k ∣ 8 := by
      norm_num at h1 ⊢
      exact h1
    have h9 : k ≤ 8 := by
      exact Int.le_of_dvd (by linarith) h8
    linarith