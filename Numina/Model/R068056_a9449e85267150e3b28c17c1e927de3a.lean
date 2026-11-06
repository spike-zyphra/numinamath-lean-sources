import Mathlib

theorem number_theory_144404 (a n p : ℕ) (hp : Nat.Prime p) (h : p ∣ a ^ n) :
    p ^ n ∣ a ^ n := by 
  have h1 : p ∣ a := by 
    apply hp.dvd_of_dvd_pow 
    exact h 
  apply pow_dvd_pow_of_dvd 
  exact h1