import Mathlib

theorem number_theory_235410 {n : ℕ} (h : 701 % n = 8 ∧ 592 % n = 7) : n = 9 := by
  rcases h with ⟨h1, h2⟩
  have h3 : n ≤ 701 := by 
    by_contra h4 
    push_neg at h4 
    have h5 : 701 % n = 701 := by 
      rw [Nat.mod_eq_of_lt] 
      all_goals omega 
    omega 
  have h4 : n ≤ 592 := by 
    by_contra h5 
    push_neg at h5 
    have h6 : 592 % n = 592 := by 
      rw [Nat.mod_eq_of_lt] 
      all_goals omega 
    omega 
  interval_cases n <;> norm_num at h1 h2 <;> omega