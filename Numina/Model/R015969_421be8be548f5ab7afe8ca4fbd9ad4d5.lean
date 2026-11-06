import Mathlib

theorem number_theory_139055 (a b c : ℕ) (hc : 1 ≤ c) :
    a ∣ b ↔ a^c ∣ b^c := by
  constructor
  · -- Assume a divides b, then a^c divides b^c.
    intro h 
    apply pow_dvd_pow_of_dvd 
    exact h 
  · -- Assume a^c divides b^c, prove a divides b 
    intro h 
    have h2 : a ∣ b := by
      have h3 : a ^ c ∣ b ^ c := h 
      have hc_ne_zero : c ≠ 0 := by 
        omega 
      apply (Nat.pow_dvd_pow_iff hc_ne_zero).mp 
      exact h3 
    exact h2