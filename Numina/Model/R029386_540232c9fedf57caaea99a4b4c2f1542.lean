import Mathlib

theorem algebra_239857 (a : ℕ → ℤ) (h₁ : a 1 = 1) (h₂ : a 2 = 3) (h₃ : ∀ n ≥ 2, a (n + 1) = 3 * a n - 2 * a (n - 1)) :
    a 1000 = 2 ^ 1000 - 1 := by
  have h4 : ∀ (n : ℕ), a (n + 1) = 2 ^ (n + 1) - 1 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [h₁]
    | succ n =>
      cases n with
      | zero =>
        simp [h₂]
      | succ n =>
        have h5 := ih (n + 1) (by omega)
        have h6 := ih (n) (by omega)
        simp [show n + 2 + 1 = n + 3 by omega] at *
        simp [h₃ (n + 2) (by omega), h5, h6]
        ring_nf
  specialize h4 999
  norm_num at h4 ⊢
  all_goals omega