import Mathlib

theorem number_theory_284496 {n : ℕ} (hn : n ≠ 0) :
    132 % n = 75 % n ∧ 75 % n = 37 % n → n ≤ 19 := by 
  intro h
  have h1 : 132 % n = 75 % n := h.1
  have h2 : 75 % n = 37 % n := h.2
  by_cases h3 : n > 132
  · 
    have h4 : 132 % n = 132 := by
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    have h5 : 75 % n = 75 := by 
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    have h6 : 132 = 75 := by 
      omega
    all_goals omega
  · 
    interval_cases n <;> norm_num at h1 h2 <;> omega