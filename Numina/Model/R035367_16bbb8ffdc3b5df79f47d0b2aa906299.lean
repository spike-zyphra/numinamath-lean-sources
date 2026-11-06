import Mathlib

open Real
open scoped BigOperators

theorem inequalities_116984 (x : ℝ) (hx : -1 < x) (n : ℕ) (hn : 0 < n) :
  (1 + x) ^ n ≥ 1 + n * x := by
  have h1 : x > -1 := by linarith
  have h2 : ∀ n : ℕ, 0 < n → (1 + x) ^ n ≥ 1 + ↑n * x := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        norm_num at *
      | succ n =>
        simp [mul_add, add_mul, pow_succ] at ih ⊢
        nlinarith [sq_nonneg (x), sq_nonneg ((1 + x) ), sq_nonneg (x * (1 + x)), hx, sq_nonneg (x + 1), mul_pos (show (0 : ℝ) < (1 + x) by linarith) (show (0 : ℝ) < (1 + x) by linarith), ih]
  specialize h2 n hn
  simpa using h2