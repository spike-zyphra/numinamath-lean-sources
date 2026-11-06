import Mathlib

open Nat

theorem inequalities_598785 (n : ℕ) (hn : 3 ≤ n) : 2^n > 2 * n + 1 := by
  have h1 : 2 ^ 3 > 2 * 3 + 1 := by norm_num
  have h2 : ∀ k : ℕ, 3 ≤ k → 2 ^ k > 2 * k + 1 → 2 ^ (k + 1) > 2 * (k + 1) + 1 := by
    intro k hk h
    have h1 : 2 ^ (k + 1) = 2 * (2 ^ k) := by ring
    rw [h1]
    have h2 : 2 * (2 ^ k) > 2 * (2 * k + 1) := by
      have h3 : 2 ^ k > 2 * k + 1 := h
      nlinarith [h3]
    have h3 : 2 * (2 * k + 1) > 2 * (k + 1) + 1 := by
      omega
    linarith [h2, h3]
  exact Nat.le_induction h1 h2 n hn