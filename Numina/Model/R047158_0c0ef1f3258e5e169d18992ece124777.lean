import Mathlib

theorem number_theory_130394 :
    IsGreatest {x | ∃ a b, x = Nat.gcd a b ∧ a * b = 14000} 20 := by 
  constructor
  · -- Show that 20 is in the set
    use 100, 140 
    all_goals norm_num
  · -- Show that 20 is greatest in the set
    intro x hx 
    rcases hx with ⟨a, b, h_eq, hx₂⟩
    have h1 : x ∣ a := by 
      have h4 : x = Nat.gcd a b := by
        exact_mod_cast h_eq 
      have h5 : x ∣ a := by 
        rw [h4] 
        apply Nat.gcd_dvd_left
      exact_mod_cast h5
    have h2 : x ∣ b := by 
      have h4 : x = Nat.gcd a b := by 
        exact_mod_cast h_eq 
      have h5 : x ∣ b := by 
        rw [h4] 
        apply Nat.gcd_dvd_right
      exact_mod_cast h5
    -- Now let's establish a * b ∣ 14000
    have h3 : x * x ∣ a * b := by 
      apply mul_dvd_mul 
      · exact h1 
      · exact h2 
    -- Now a standard proof
    have h4 : x * x ∣ 14000 := by 
      rw [show a * b = 14000 by exact hx₂] at h3 
      exact_mod_cast h3 
    have h5 : x ≤ 20 := by  
      by_contra h 
      push_neg at h 
      have h6 : x ≥ 21 := by 
        omega 
      have h7 : x * x ≥ 441 := by 
        nlinarith 
      -- We need to derive a contradiction between h and h7
      have h8 : x ≤ 118 := by 
        have h9 : x * x ≤ 14000 := by 
          have h8 : x * x ∣ 14000 := h4 
          exact Nat.le_of_dvd (by norm_num) h8 
        nlinarith 
      interval_cases x <;> norm_num at h4 h7 h8 
    linarith [h5, h_eq]