import Mathlib

theorem number_theory_275783 (a b c : ℤ) (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b) (hc : ¬ 3 ∣ c) :
    3 ∣ a^2 + b^2 + c^2 := by 
  have h1 : a % 3 = 1 ∨ a % 3 = 2 := by 
    omega 
  have h2 : b % 3 = 1 ∨ b % 3 = 2 := by 
    omega 
  have h3 : c % 3 = 1 ∨ c % 3 = 2 := by 
    omega 
  have ha2 : a^2 % 3 = 1 := by
    rcases h1 with (h | h)
    · -- if a % 3 = 1
      simp [pow_two, Int.add_emod, Int.mul_emod, h]
    · -- if a % 3 = 2
      simp [pow_two, Int.add_emod, Int.mul_emod, h]
  have hb2 : b^2 % 3 = 1 := by
    rcases h2 with (h | h)
    · -- if b % 3 = 1
      simp [pow_two, Int.add_emod, Int.mul_emod, h]
    · -- if b % 3 = 2
      simp [pow_two, Int.add_emod, Int.mul_emod, h]
  have hc2 : c^2 % 3 = 1 := by
    rcases h3 with (h | h)
    · -- if c % 3 = 1
      simp [pow_two, Int.add_emod, Int.mul_emod, h]
    · -- if c % 3 = 2
      simp [pow_two, Int.add_emod, Int.mul_emod, h]
  have h4 : (a^2 + b^2 + c^2) % 3 = 0 := by
    omega
  exact Int.dvd_of_emod_eq_zero h4