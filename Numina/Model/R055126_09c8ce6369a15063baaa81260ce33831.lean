import Mathlib

theorem algebra_21509 (x : ℕ) (hx : x ≠ 0) (h : 18 % x = 0 ∧ 24 % x = 0) :
    x ≤ 6 := by
  have h1 : x ∣ 18 := by
    exact Nat.dvd_of_mod_eq_zero h.1
  have h2 : x ∣ 24 := by
    exact Nat.dvd_of_mod_eq_zero h.2
  have h3 : x ∣ Nat.gcd 18 24 := by 
    exact Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd 18 24 = 6 := by 
    norm_num [Nat.gcd]
  rw [h4] at h3
  have h5 : x ≤ 6 := by 
    exact Nat.le_of_dvd (show 6 > 0 by norm_num) h3
  linarith