import Mathlib

theorem number_theory_2371 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a > b) :
    Nat.lcm a b ≥ a ∧ a > b ∧ b ≥ Nat.gcd a b := by
  constructor
  · -- Show that $\text{lcm } a b \geq a.$
    have h1 : a ∣ Nat.lcm a b := by 
      exact Nat.dvd_lcm_left a b 
    have h2 : 0 < Nat.lcm a b := by 
      apply Nat.lcm_pos 
      all_goals 
        try omega 
    have h3 : a ≤ Nat.lcm a b := by 
      apply (Nat.le_of_dvd (by linarith) h1)
    linarith 
  constructor
  · -- Show that $a > b$ 
    exact h 
  · -- Show that $b \geq \text{gcd } a b$ 
    have h4 : Nat.gcd a b ∣ b := by 
      apply Nat.gcd_dvd_right 
    have h5 : 0 < b := hb 
    have h6 : Nat.gcd a b ≤ b := by 
      exact Nat.le_of_dvd (by linarith) h4 
    linarith