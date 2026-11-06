import Mathlib

theorem number_theory_164371 (a b : ℕ) :
    Nat.lcm a b % Nat.gcd a b = 0 := by
  have h1 : Nat.gcd a b ∣ Nat.lcm a b := by
    have h2 : Nat.gcd a b ∣ a := by 
      exact Nat.gcd_dvd_left a b
    have h3 : a ∣ Nat.lcm a b := by
      exact Nat.dvd_lcm_left a b
    exact dvd_trans h2 h3
  exact Nat.dvd_iff_mod_eq_zero.mp h1