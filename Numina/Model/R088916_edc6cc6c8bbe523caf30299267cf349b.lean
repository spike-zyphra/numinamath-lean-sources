import Mathlib

theorem number_theory_154750 (p a b : ℤ) (hp : Prime p) (hpa : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by 
  exact hp.dvd_or_dvd hpa