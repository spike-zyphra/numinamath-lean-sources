import Mathlib

theorem algebra_21954 {a : ℕ → ℝ} (ha1 : a 1 = 1) (ha2 : a 2 = 2)
    (han : ∀ n ≥ 2, a n ^ 2 - a (n - 1) * a (n + 1) = 1) :
    a 100 = 100 := by
  have h1 : ∀ (n : ℕ), a (n + 1) = (n + 1 : ℝ) := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      norm_num [ha1]
    | succ n =>
      cases n with
      | zero =>
        norm_num [ha2]
      | succ n =>
        have h3 : a 3 = 3 := by
          specialize han 2 (by norm_num)
          norm_num [ha1, ha2] at han ⊢
          linarith
        have eq1 := ih (n) (by linarith)
        have eq2 := ih (n + 1) (by linarith)
        have h3 := han (n + 2) (by linarith)
        simp [show n + 2 ≥ 2 by linarith] at h3
        norm_num [eq1, eq2] at h3 ⊢
        nlinarith
  specialize h1 99
  norm_num at h1 ⊢
  linarith