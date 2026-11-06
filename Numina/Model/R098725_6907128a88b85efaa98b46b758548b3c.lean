import Mathlib

theorem number_theory_5322 (a b : ℤ) (ha : Odd a) (hb : Odd b) :
  8 ∣ a^2 - b^2 := by 
  have h1 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by 
    rcases ha with ⟨k, hk⟩ 
    omega 
  have h2 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by 
    rcases hb with ⟨k, hk⟩ 
    omega 
  have h3 : a^2 % 8 = 1 := by 
    rcases h1 with (h1 | h1 | h1 | h1)
    · simp [pow_two, Int.mul_emod, h1, Int.add_emod, Int.mul_emod]
    · simp [pow_two, Int.mul_emod, h1, Int.add_emod, Int.mul_emod]
    · simp [pow_two, Int.mul_emod, h1, Int.add_emod, Int.mul_emod]
    · simp [pow_two, Int.mul_emod, h1, Int.add_emod, Int.mul_emod]
  have h4 : b^2 % 8 = 1 := by 
    rcases h2 with (h2 | h2 | h2 | h2)
    · simp [pow_two, Int.mul_emod, h2, Int.add_emod, Int.mul_emod]
    · simp [pow_two, Int.mul_emod, h2, Int.add_emod, Int.mul_emod]
    · simp [pow_two, Int.mul_emod, h2, Int.add_emod, Int.mul_emod]
    · simp [pow_two, Int.mul_emod, h2, Int.add_emod, Int.mul_emod]
  have h5 : (a^2 - b^2) % 8 = 0 := by 
    omega 
  exact Int.dvd_of_emod_eq_zero h5