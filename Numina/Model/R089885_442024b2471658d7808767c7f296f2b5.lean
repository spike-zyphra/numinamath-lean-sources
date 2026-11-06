import Mathlib

open Finset

theorem algebra_197340 {x : ℕ → ℝ} (hx0 : x 0 = 1)
    (hxn : ∀ n, x (n + 1) = x n / (x n + 1)) :
    ∀ n, x n = 1 / (n + 1) := by
  intro n
  induction n with
  | zero =>
    simp [hx0]
  | succ n ih =>
    have eq1 : x (n + 1) = x n / (x n + 1) := hxn n
    rw [eq1]
    rw [ih]
    field_simp
    <;> ring_nf <;> field_simp
    <;> ring