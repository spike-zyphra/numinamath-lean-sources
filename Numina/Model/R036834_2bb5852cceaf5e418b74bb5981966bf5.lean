import Mathlib

theorem number_theory_288739 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    gcd a b ∣ a ∧ gcd a b ∣ b := by 
  constructor
  · -- Show that gcd a b divides a
    apply Nat.gcd_dvd_left
  · -- Show that gcd a b divides b
    apply Nat.gcd_dvd_right