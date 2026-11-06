import Mathlib

theorem algebra_15782 {x : ℕ} (hx : x ≠ 0) (h : 18 % x = 0 ∧ 24 % x = 0) (h' : x ≥ 4) :
    x = 6 := by
  have h1 : x ∣ 18 := by
    exact Nat.dvd_of_mod_eq_zero h.1
  have h2 : x ∣ 24 := by
    exact Nat.dvd_of_mod_eq_zero h.2
  have h3 : x ∣ 6 := by
    exact Nat.dvd_gcd h1 h2
  have h4 : x ≤ 6 := by
    exact Nat.le_of_dvd (show 0 < 6 by norm_num) h3
  interval_cases x <;> norm_num at *
  <;> try contradiction