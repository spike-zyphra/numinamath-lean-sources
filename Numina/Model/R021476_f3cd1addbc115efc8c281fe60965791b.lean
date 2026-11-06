import Mathlib

theorem number_theory_7984 :
    IsGreatest {n | ∀ a b : ℤ, Odd a → Odd b → n ∣ (a^2 - b^2)} 8 := by
  constructor
  · -- Show 8 is in the set.
    show ∀ a b : ℤ, Odd a → Odd b → 8 ∣ (a^2 - b^2)
    intro a b ha1 ha2
    have h1 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by 
      rcases ha1 with ⟨k, hk⟩
      have : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
        omega
      assumption
    have h2 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by 
      rcases ha2 with ⟨k, hk⟩
      have : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by
        omega
      assumption
    have h3 : a^2 % 8 = 1 := by 
      rcases h1 with (h | h | h | h)
      · -- case a % 8 = 1
        simp [h, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
      · -- case a % 8 = 3
        simp [h, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
      · -- case a % 8 = 5
        simp [h, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
      · -- case a % 8 = 7
        simp [h, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
    have h4 : b^2 % 8 = 1 := by 
      rcases h2 with (h | h | h | h)
      · -- case b % 8 = 1
        simp [h, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
      · -- case b % 8 = 3
        simp [h, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
      · -- case b % 8 = 5
        simp [h, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
      · -- case b % 8 = 7
        simp [h, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
    have h5 : (a^2 - b^2) % 8 = 0 := by 
      omega
    exact Int.dvd_of_emod_eq_zero h5
  · -- Show 8 is greatest in the set.
    intro n hn
    have h1 := hn 3 1 (by decide) (by decide)
    have h2 : n ∣ 8 := by 
      exact h1
    have h3 : n ≤ 8 := by 
      exact Int.le_of_dvd (by norm_num) h2
    linarith