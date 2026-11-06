import Mathlib

theorem algebra_12533
    (a : ℕ → ℝ)
    (h₀ : a 1 = 1)
    (h₁ : a 2 = 1 / 2)
    (h₂ : ∀ n ≥ 2, a n * (a (n - 1) + a (n + 1)) = 2 * a (n + 1) * a (n - 1))
    : a 2012 = 1 / 2012 := by

  have h3 : ∀ n : ℕ, a (n + 1) = 1 / (n + 1 : ℝ) := by
    intro n 
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      norm_num [h₀]
    | succ n =>
      cases n with
      | zero =>
        norm_num [h₁]
      | succ n =>
        have eq1 := h₂ (n + 2) (by linarith)
        have h4 := ih (n) (by linarith)
        have h5 := ih (n + 1) (by linarith)
        simp [show n + 1 + 1 = n + 2 by omega] at eq1 h4 h5 ⊢
        field_simp [h4, h5] at eq1 ⊢
        ring_nf at eq1 ⊢
        nlinarith

  have h4 := h3 2011
  norm_num at h4 ⊢
  linarith