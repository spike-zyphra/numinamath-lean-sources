import Mathlib

theorem number_theory_164856 :
    IsGreatest {n | ∃ k, n = k ∧ 120 % n = 0 ∧ 140 % n = 0} 20 := by 
  constructor
  · -- Show 20 is in the set.
    use 20
    all_goals norm_num
  · -- Show 20 is greatest in the set.
    intro n hn
    rcases hn with ⟨k, rfl, h1, h2⟩
    have h1' : n ∣ 120 := by 
      exact Nat.dvd_of_mod_eq_zero h1
    have h2' : n ∣ 140 := by 
      exact Nat.dvd_of_mod_eq_zero h2
    -- From h1' and h2', we have n divides gcd(120, 140)
    have h4 : n ∣ 20 := by 
      exact Nat.dvd_gcd h1' h2'
    -- Show n ≤ 20 
    have h8 : n ≤ 20 := by
      have h6 : n ∣ 20 := h4 
      have h7 : n > 0 := by 
        by_contra h
        push_neg at h
        have h8 : n = 0 := by linarith
        rw [h8] at h1 
        all_goals omega 
      have h8 : n ≤ 20 := by 
        exact Nat.le_of_dvd (by norm_num) h6 
      linarith 
    -- Final goal
    linarith