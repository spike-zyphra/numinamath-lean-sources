import Mathlib

theorem algebra_137053 {α : ℝ} (hα : α ≠ 0) (h : ∃ k : ℤ, α + 1/α = k) (n : ℕ) :
    ∃ m : ℤ, α^n + 1/α^n = m := by 
  rcases h with ⟨k, hk⟩
  have h1 : ∀ n : ℕ, ∃ m : ℤ, α ^ n + 1 / α ^ n = m := by
    intro n 
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero => 
      use 2
      norm_num 
    | succ n => 
      cases n with 
      | zero => -- n = 1
        use k 
        field_simp [hα] at hk ⊢ 
        all_goals 
          try linarith 
      | succ n => 
        cases n with 
        | zero => -- n = 2
          have eq2 : α ^ 2 + 1 / α ^ 2 = (k : ℝ) ^ 2 - 2 := by 
            have eq3 : α + 1 / α = (k : ℝ) := by 
              simpa using hk 
            have eq4 : α ^ 2 + 1 / α ^ 2 = (α + 1 / α) ^ 2 - 2 := by 
              field_simp [hα]
              linarith 
            rw [eq4] 
            rw [eq3] 
          refine ⟨k ^ 2 - 2, by 
            rw [eq2] 
            simp 
          ⟩ 
        | succ n => -- n >= 3
          have h2 := ih (n + 2) (by linarith)
          have h1 := ih (n + 1) (by linarith)
          rcases h2 with ⟨m2, hm2⟩
          rcases h1 with ⟨m1, hm1⟩
          have eq1 : α ^ (n + 3) + 1 / α ^ (n + 3) = (α ^ (n + 2) + 1 / α ^ (n + 2)) * (α + 1 / α) - (α ^ (n + 1) + 1 / α ^ (n + 1)) := by 
            field_simp [hα]
            ring 
          rw [eq1] 
          rw [hm2] 
          rw [hm1] 
          rw [hk] 
          use m2 * k - m1 
          all_goals 
            try norm_num 
            <;> ring_nf 
  specialize h1 n 
  simpa using h1