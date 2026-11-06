import Mathlib

theorem algebra_120007 {α : ℝ} (hα : α ≠ 0) (hα' : ∃ m : ℤ, α + 1 / α = m) (n : ℕ) : ∃ p : ℤ, α^n + 1 / α^n = p := by 
  rcases hα' with ⟨m, hm⟩
  have h1 : ∀ (n : ℕ), ∃ p : ℤ, α ^ n + 1 / α ^ n = p := by
    intro n 
    have h2 : ∀ (n : ℕ), ∃ p : ℤ, α ^ n + 1 / α ^ n = p := by
      intro n 
      induction' n using Nat.strongRecOn with n ih 
      cases n with 
      | zero =>
        use 2
        have h4 : α ^ 0 + 1 / α ^ 0 = (2 : ℝ) := by 
          field_simp [hα]
          <;> norm_num 
        rw [h4] 
        all_goals norm_num 
      | succ n =>
        cases n with 
        | zero =>
          have h3 : (α + 1 / α) = (m : ℝ) := by 
            exact_mod_cast hm 
          refine ⟨m, by 
            field_simp [hα] at h3 ⊢ 
            linarith 
          ⟩ 
        | succ n =>
          rcases ih (n + 1) (by linarith) with ⟨p1, hp1⟩ 
          rcases ih (n) (by linarith) with ⟨p2, hp2⟩ 
          use m * p1 - p2 
          have eq1 : α ^ (n + 2 : ℕ) + 1 / α ^ (n + 2 : ℕ) = (α + 1 / α) * (α ^ (n + 1 : ℕ) + 1 / α ^ (n + 1 : ℕ)) - (α ^ (n : ℕ) + 1 / α ^ (n : ℕ)) := by 
            field_simp [hα] 
            <;> ring 
          rw [eq1] 
          rw [hm] 
          rw [hp1] 
          rw [hp2] 
          all_goals norm_num 
          all_goals ring
    specialize h2 n 
    simpa using h2 
  specialize h1 n 
  simpa using h1