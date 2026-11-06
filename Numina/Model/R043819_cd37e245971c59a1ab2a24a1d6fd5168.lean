import Mathlib

open Finset Real Nat

theorem algebra_221018 {a : ℕ → ℝ}
    (ha0 : a 0 = 2)
    (han : ∀ n > 0, a n = a (n - 1) - n / (n + 1)!) :
    ∀ n, a n = 1 + 1 / (n + 1)! := by
  intro n 
  induction n with
  | zero =>
    -- Base case: n = 0
    rw [ha0]
    norm_num 
  | succ n ih =>
    -- Inductive step: Assume the formula holds for n, prove for n+1
    have h1 : a (n + 1) = a n - (n + 1) / ((n + 1) + 1) ! := by
      specialize han (n + 1) (by linarith)
      simpa using han 
    rw [h1]
    rw [ih]
    field_simp [Nat.factorial] 
    <;> ring