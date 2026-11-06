import Mathlib

theorem algebra_325138 {a : ℕ → ℝ} (ha1 : a 1 = 2) (ha2 : a 2 = 1)
    (han : ∀ n > 0, a (n + 2) = ((n * (n + 1) * a (n + 1) + n ^ 2 * a n + 5) / (n + 2)) - 2) :
    ∀ n > 0, a n = ((Nat.factorial (n - 1) + 1) / n) := by
  intro n hn
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero => 
    linarith
  | succ n => 
    cases n with
    | zero => 
      -- n = 1
      rw [ha1]
      norm_num [Nat.factorial]
    | succ n => 
      cases n with
      | zero => 
        -- n = 2
        rw [ha2]
        norm_num [Nat.factorial]
      | succ n => 
        have eq1 := ih (n + 1) (by linarith)
        have eq2 := ih (n + 2) (by linarith)
        have h3 := han (n + 1) (by linarith)
        simp [show n + 1 + 2 = n + 3 by omega] at h3 ⊢
        simp [h3, eq1, eq2]
        field_simp [Nat.factorial] at *
        ring_nf at *
        <;> norm_num [Nat.factorial] at *
        <;> field_simp at *
        <;> ring_nf <;> norm_num