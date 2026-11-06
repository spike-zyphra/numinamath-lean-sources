import Mathlib

theorem number_theory_275417 (a b c : ℤ) (h₀ : 0 < c) (h₁ : a % c = b % c) :
    c ∣ a - b := by 
  have h2 : (a - b) % c = 0 := by
    simp [Int.sub_emod, h₁]
  exact Int.dvd_of_emod_eq_zero h2