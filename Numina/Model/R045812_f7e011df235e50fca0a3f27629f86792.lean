import Mathlib

theorem number_theory_242860 : IsGreatest {N | (Nat.factorial N) % 10^2013 = 0 ∧ ¬(Nat.factorial N) % 10^2014 = 0} 8069 := by
  constructor
  · -- Show that 8069 is in the set.
    constructor
    · -- Check that (Nat.factorial 8069) % 10^2013 = 0.
      native_decide
    · -- Check that ¬(Nat.factorial 8069) % 10^2014 = 0.
      native_decide
  · -- Show that 8069 is greatest in the set.
    intro N hN
    rcases hN with ⟨hN1, hN2⟩
    by_contra h
    push_neg at h 
    have hN3 : N ≥ 8070 := by 
      omega 
    have hN4 : (Nat.factorial N) % 10^2014 = 0 := by
      have hN5 : N ≥ 8070 := hN3
      have h8 : (Nat.factorial 8070) % 10^2014 = 0 := by 
        native_decide 
      have h6 : (Nat.factorial N) % 10^2014 = 0 := by 
        have hN6 : N ≥ 8070 := hN5
        have h7 : (Nat.factorial 8070) % 10^2014 = 0 := h8 
        have h9 : (10^2014) ∣ (Nat.factorial 8070) := by 
          omega 
        have h10 : (10^2014) ∣ (Nat.factorial N) := by 
          have h11 : (Nat.factorial 8070) ∣ (Nat.factorial N) := by 
            apply Nat.factorial_dvd_factorial 
            all_goals 
            omega 
          have h12 : (10^2014) ∣ (Nat.factorial 8070) := h9 
          exact dvd_trans h12 h11 
        exact Nat.dvd_iff_mod_eq_zero.mp h10 
      exact h6 
    have hN5 : (Nat.factorial N) % 10^2014 = 0 := hN4 
    have hN6 : ¬ (Nat.factorial N) % 10^2014 = 0 := hN2 
    exact hN6 hN5