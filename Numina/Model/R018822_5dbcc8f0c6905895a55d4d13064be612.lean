import Mathlib

theorem algebra_603015 (a : ℕ → ℤ) (ha : a 0 > 0) (h1 : a 1 > a 0)
    (h2 : ∀ n, a (n + 2) = 3 * a (n + 1) - 2 * a n) :
    a 100 > 2 ^ 99 := by

  have h100 : ∀ (n : ℕ), a n = (2 * a 0 - a 1) + (a 1 - a 0) * (2 ^ n) := by 
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero => 
      simp 
      all_goals linarith
    | succ n => 
      cases n with
      | zero => 
        simp
        all_goals linarith
      | succ n => 
        have h1' := ih (n) (by linarith)
        have h2' := ih (n + 1) (by linarith)
        simp [h2, h1', h2']
        all_goals ring

  have h300 : a 100 = (2 * a 0 - a 1) + (a 1 - a 0) * (2 ^ 100) := h100 100

  rw [h300]

  have h3 : a 1 - a 0 > 0 := by linarith

  have h6 : (a 1 - a 0) ≥ 1 := by omega

  omega