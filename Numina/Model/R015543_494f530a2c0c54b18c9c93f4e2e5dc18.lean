import Mathlib

theorem number_theory_78065 (n : ℕ) (hn : 0 < n) :
    8 ∣ 5^n + 2 * 3^(n - 1) + 1 := by 
  have h1 : ∀ (n : ℕ), 0 < n → 8 ∣ 5^n + 2 * 3^(n - 1) + 1 := by 
    intro n hn
    induction' n using Nat.strongRecOn with n ih 
    cases n with
    | zero => 
      exfalso
      linarith 
    | succ n => 
      cases n with 
      | zero => 
        norm_num 
      | succ n => 
        cases n with 
        | zero => 
          norm_num 
        | succ n => 
          have h1 := ih (n) (by linarith)
          have h2 := ih (n + 1) (by linarith)
          simp [pow_succ, pow_zero] at h1 h2 ⊢ 
          all_goals 
            omega 
  specialize h1 n hn
  simpa using h1