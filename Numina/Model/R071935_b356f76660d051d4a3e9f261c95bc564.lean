import Mathlib

open Finset

theorem number_theory_117260 {x : ℕ → ℕ}
    (h₀ : ∀ n, x (2 * n) = x n)
    (h₁ : ∀ n, x (2 * n + 1) = 1 - x (2 * n))
    (h₂ : ∀ n, x n = 1 - x (n - 2 ^ (Nat.factorization n 2))) :
    x 1993 = 0 := by
  have h3 := h₂ 0
  have h4 := h₂ 1
  have h5 := h₀ 0
  have h6 := h₁ 0
  norm_num [Nat.factorization] at h3 h4 h5 h6 ⊢ <;> omega