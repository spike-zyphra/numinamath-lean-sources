import Mathlib

open Finset

theorem algebra_200875 (a : ℕ → ℕ → ℚ)
    (h₀ : ∀ n, a n 0 = 1 / (n + 1))
    (h₁ : ∀ n, ∀ m, a n (m + 1) = a n m - a (n - 1) m) :
    a 1992 0 = 1 / 1993 := by
  have h1992 : a 1992 0 = 1 / (1992 + 1 : ℚ) := h₀ 1992
  rw [h1992]
  norm_num