import Mathlib

theorem other_73111 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = 2 * a n + Real.sqrt (3 * (a n)^2 + 1)) :
    ∀ n ≥ 1, ∃ m : ℤ, a n = m := by
  intro n hn
  have h1 : ∀ (n : ℕ), n ≥ 1 → ∃ m : ℤ, a n = m := by
    intro n hn 
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      exfalso 
      linarith
    | succ n =>
      cases n with 
      | zero =>
        use 1 
        all_goals norm_num [ha1]
      | succ n =>
        cases n with 
        | zero =>
          use 4 
          have h2 := han 1 (by norm_num)
          rw [ha1] at h2 
          have h6 : Real.sqrt (3 * (1 : ℝ) ^ 2 + 1) = (2 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h6] at h2 
          norm_num at h2 ⊢
          all_goals linarith
        | succ n => 
          have eq1 : a (n + 3) = 2 * a (n + 2) + Real.sqrt (3 * (a (n + 2)) ^ 2 + 1) := by 
            specialize han (n + 2) (by linarith)
            simpa using han
          have eq4 : a (n + 1) ≥ 0 := by
            have h8 := ha1
            have h9 := han 1 (by norm_num)
            norm_num [h8] at h9
            have h10 : n + 1 ≥ 1 := by omega
            have h11 : ∀ m ≥ 1, a m ≥ 0 := by
              intro m hm
              induction m with 
              | zero => 
                linarith
              | succ m ih =>
                cases m with
                | zero => 
                  rw [ha1]
                  all_goals linarith
                | succ m => 
                  have eq100 := han (m + 1) (by linarith)
                  rw [eq100]
                  nlinarith [Real.sqrt_nonneg (3 * a (m + 1) ^ 2 + 1), Real.sq_sqrt (show 0 ≤ 3 * a (m + 1) ^ 2 + 1 by nlinarith), ih (by linarith)]
            specialize h11 (n + 1) (by linarith)
            linarith
          have h3 : a (n + 2) = 2 * a (n + 1) + Real.sqrt (3 * (a (n + 1)) ^ 2 + 1) := by
            specialize han (n + 1) (by linarith)
            simpa using han
          have eq2 : Real.sqrt (3 * (a (n + 2)) ^ 2 + 1) = 2 * a (n + 2) - a (n + 1) := by
            have h_eq : (2 * a (n + 2) - a (n + 1)) ^ 2 = 3 * (a (n + 2)) ^ 2 + 1 := by
              rw [show a (n + 2) = 2 * a (n + 1) + Real.sqrt (3 * (a (n + 1)) ^ 2 + 1) by linarith [h3]]
              nlinarith [Real.sqrt_nonneg (3 * (a (n + 1)) ^ 2 + 1), Real.sq_sqrt (show 0 ≤ 3 * (a (n + 1)) ^ 2 + 1 by nlinarith)]
            have h_nonneg : 2 * a (n + 2) - a (n + 1) ≥ 0 := by 
              rw [show a (n + 2) = 2 * a (n + 1) + Real.sqrt (3 * (a (n + 1)) ^ 2 + 1) by linarith [h3]]
              nlinarith [Real.sqrt_nonneg (3 * (a (n + 1)) ^ 2 + 1), Real.sq_sqrt (show 0 ≤ 3 * (a (n + 1)) ^ 2 + 1 by nlinarith)]
            have h_sq : (Real.sqrt (3 * (a (n + 2)) ^ 2 + 1)) ^ 2 = (2 * a (n + 2) - a (n + 1)) ^ 2 := by
              rw [Real.sq_sqrt (by nlinarith)]
              linarith [h_eq]
            have h_nonneg_sqrt : Real.sqrt (3 * (a (n + 2)) ^ 2 + 1) ≥ 0 := by positivity
            nlinarith [h_nonneg, h_nonneg_sqrt, h_sq]
          have eq3 : a (n + 3) = 4 * a (n + 2) - a (n + 1) := by
            rw [eq1]
            rw [eq2]
            all_goals ring
          have eq31 : ∃ m : ℤ, a (n + 1) = m := by 
            apply ih (n + 1)
            all_goals 
              omega
          have eq32 : ∃ m : ℤ, a (n + 2) = m := by 
            apply ih (n + 2) 
            all_goals 
              omega
          rcases eq31 with ⟨z₁, hz₁⟩ 
          rcases eq32 with ⟨z₂, hz₂⟩ 
          use (4 * z₂ - z₁)
          have eq4 : a (n + 3) = (4 * ↑z₂ - ↑z₁) := by
            have eq5 : a (n + 1) = (↑z₁ : ℝ) := by exact_mod_cast hz₁
            have eq6 : a (n + 2) = (↑z₂ : ℝ) := by exact_mod_cast hz₂
            nlinarith [eq3, eq5, eq6]
          norm_num at eq4 ⊢
          all_goals linarith
  specialize h1 n hn
  simpa using h1