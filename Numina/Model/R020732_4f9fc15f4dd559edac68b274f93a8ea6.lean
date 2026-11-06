import Mathlib

theorem number_theory_214471 (a b c : ℤ) (ha : Odd a) (hb : Odd b) (hc : Odd c) :
    4 ∣ (a * b - 1) ∨ 4 ∣ (b * c - 1) ∨ 4 ∣ (c * a - 1) := by

  have ha1 : a % 4 = 1 ∨ a % 4 = 3 := by 
    have h1 : a % 2 = 1 := by 
      rcases ha with ⟨k, hk⟩ 
      omega 
    omega

  have hb1 : b % 4 = 1 ∨ b % 4 = 3 := by 
    have h1 : b % 2 = 1 := by 
      rcases hb with ⟨k, hk⟩ 
      omega 
    omega

  have hc1 : c % 4 = 1 ∨ c % 4 = 3 := by 
    have h1 : c % 2 = 1 := by 
      rcases hc with ⟨k, hk⟩ 
      omega 
    omega

  rcases ha1 with ha1 | ha1 <;> rcases hb1 with hb1 | hb1 <;> rcases hc1 with hc1 | hc1 <;> simp [Int.dvd_iff_emod_eq_zero, Int.sub_emod, Int.mul_emod, ha1, hb1, hc1] <;> omega