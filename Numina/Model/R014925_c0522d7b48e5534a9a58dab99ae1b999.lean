import Mathlib

theorem number_theory_210946 (a b c : ℤ) (ha : Odd a) (hb : Odd b) (hc : Odd c) :
    4 ∣ (a * b - 1) ∨ 4 ∣ (b * c - 1) ∨ 4 ∣ (c * a - 1) := by 
  have h1 : a % 4 = 1 ∨ a % 4 = 3 := by 
    rcases ha with ⟨k, hk⟩
    omega 
  have h2 : b % 4 = 1 ∨ b % 4 = 3 := by 
    rcases hb with ⟨k, hk⟩ 
    omega 
  have h3 : c % 4 = 1 ∨ c % 4 = 3 := by
    rcases hc with ⟨k, hk⟩
    omega 
  rcases h1 with (ha1 | ha1) <;> rcases h2 with (hb1 | hb1) <;> rcases h3 with (hc1 | hc1) <;> 
    ( 
      simp [Int.dvd_iff_emod_eq_zero, Int.sub_emod, Int.mul_emod, ha1, hb1, hc1] 
      <;> omega 
    )