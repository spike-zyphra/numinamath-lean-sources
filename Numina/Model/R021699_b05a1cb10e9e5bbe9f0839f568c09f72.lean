import Mathlib

theorem algebra_308697 {n : ℕ} (hn : n > 0) (h : ∃ k, k = n.choose 2 ∧ k = 15) :
    n = 6 := by
  rcases h with ⟨k, hk1, hk2⟩
  have eq1 : n.choose 2 = 15 := by
    omega 
  have h2 : n ≤ 6 := by 
    by_contra h3 
    push_neg at h3
    have h8 : n ≥ 7 := by 
      omega 
    have eq2 : n.choose 2 ≥ 21 := by 
      have eq6 : n ≥ 7 := by 
        omega 
      have eq3 : n.choose 2 = n * (n - 1) / 2 := by 
        rw [Nat.choose_two_right]
        all_goals omega 
      -- Let's compute binomial coefficient value for n >= 2
      have h7 : n.choose 2 ≥ 21 := by
        have h8 : n ≥ 7 := eq6 
        rw [eq3]
        have h8' : n ≥ 7 := by omega 
        have hk3 : n * (n - 1) ≥ 7 * 6 := by 
          have h77 : n - 1 ≥ 6 := by 
            omega 
          have hk4 : n ≥ 7 := by 
            omega 
          nlinarith
        have hk5 : n * (n - 1) ≥ 42 := by 
          omega 
        have hk6 : n * (n - 1) / 2 ≥ 21 := by 
          have eq5 : n * (n - 1) ≥ 42 := by 
            omega 
          have h72 : n * (n - 1) / 2 ≥ 21 := by 
            omega 
          linarith
        omega 
      linarith 
    have h10 : n.choose 2 = 15 := by 
      omega 
    omega 
  interval_cases n <;> simp [Nat.choose] at eq1 <;> try { 
    omega 
  }