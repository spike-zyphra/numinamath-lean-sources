import Mathlib

theorem number_theory_106308 {a b : ℕ} (hb : b ≠ 0) (h1 : Nat.lcm a b = 10) (h2 : Nat.gcd a (b + 2) = 12) :
    Nat.gcd a (2 * b) + Nat.gcd a (3 * b) = 50 := by
  have h3 : a ∣ 10 := by
    have h4 : a ∣ Nat.lcm a b := by 
      apply Nat.dvd_lcm_left
    rw [h1] at h4
    exact h4
  have h4 : Nat.gcd a (b + 2) ∣ a := by 
    apply Nat.gcd_dvd_left
  rw [h2] at h4
  have h5 : 12 ∣ a := by 
    exact h4
  have h6 : a ≤ 10 := by 
    exact Nat.le_of_dvd (by norm_num) h3 
  interval_cases a <;> omega