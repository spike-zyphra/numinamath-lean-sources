import Mathlib

def u1 : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => u1 n + u1 (n + 1)

theorem number_theory_4543 {n} (hn : n > 0) : u1 (n + 1) * u1 (n - 1) - u1 n ^ 2 = (-1) ^ n := by
  have h1 : ∀ n : ℕ, n > 0 → u1 (n + 1) * u1 (n - 1) - u1 n ^ 2 = (-1) ^ n := by 
    intro n hn
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero => 
      exfalso 
      exact Nat.lt_irrefl 0 (by linarith)
    | succ n =>
      cases n with 
      | zero => 
        -- n = 1
        norm_num [u1] at *
      | succ n => 
        cases n with 
        | zero => 
          -- n = 2
          norm_num [u1] at *
        | succ n => 
          have h3 := ih (n + 1) (by linarith)
          have h4 := ih (n + 2) (by linarith)
          simp [u1] at h3 h4 ⊢
          all_goals
            ring_nf at h3 h4 ⊢
            <;> norm_num at h3 h4 ⊢
            <;> nlinarith [sq_nonneg (u1 (n + 1) - u1 (n + 2)), sq_nonneg (u1 (n + 1)), sq_nonneg (u1 (n + 2))]
  specialize h1 n hn
  simpa using h1