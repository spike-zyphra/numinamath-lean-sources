import Mathlib

theorem algebra_215723 (a : ℕ → ℝ)
    (h₀ : a 1 = 5)
    (h₁ : a 2 = 19)
    (h₂ : ∀ n ≥ 3, a n = 5 * a (n - 1) - 6 * a (n - 2)) :
    a 2007 = 3 ^ 2008 - 2 ^ 2008 := by

  have h3 : ∀ (n : ℕ), n ≥ 1 → a n = 3 ^ (n + 1) - 2 ^ (n + 1) := by
    intro n hn
    induction' n using Nat.strongRecOn with n ih 
    cases n with
    | zero => 
      exfalso
      linarith
    | succ n => 
      cases n with
      | zero => 
        rw [h₀]
        norm_num
      | succ n => 
        cases n with
        | zero => 
          rw [h₁]
          norm_num 
        | succ n => 
          have eq1 : a (n + 3) = 5 * a (n + 2) - 6 * a (n + 1) := by 
            specialize h₂ (n + 3) (by linarith)
            simpa using h₂
          have eq4 : n + 1 ≥ 1 := by omega
          have eq5 : n + 2 ≥ 1 := by omega
          have eq2 := ih (n + 2) (by 
            have : n + 2 < n + 3 := by omega
            linarith
          ) (by
            omega
          )
          have eq3 := ih (n + 1) (by 
            have : n + 1 < n + 3 := by omega
            linarith
          ) (by 
            omega
          )
          rw [show n + 1 + 1 + 1 = n + 3 by omega]
          rw [eq1]
          rw [eq2]
          rw [eq3]
          ring_nf 
  have h4 := h3 2007 (by omega)
  rw [h4]
  <;> norm_num