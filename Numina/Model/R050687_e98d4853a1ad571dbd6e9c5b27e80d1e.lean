import Mathlib

theorem number_theory_7131 (p a b : ℤ) (hp : Prime p)
    (h : p ∣ a^2 + a * b + b^2) :
    p ∣ a^3 - b^3 := by 
  have h1 : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := by
    ring
  rw [h1]
  apply dvd_mul_of_dvd_right 
  exact h