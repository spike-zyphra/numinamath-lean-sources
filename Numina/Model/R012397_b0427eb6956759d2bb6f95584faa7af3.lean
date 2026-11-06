import Mathlib

open Real
open scoped BigOperators

theorem inequalities_212988 (x : ℝ) (hx : -1 ≤ x) (n : ℕ) :
  (1 + x) ^ n ≥ 1 + n * x := by
  have h1 : ∀ (n : ℕ), (1 + x) ^ n ≥ 1 + (n : ℝ) * x := by
    intro n 
    induction n with 
    | zero =>
      simp 
    | succ k ih =>
      simp [pow_succ, mul_add, mul_one] at ih ⊢
      nlinarith [sq_nonneg x, sq_nonneg ((1 + x) - 1), hx, sq_nonneg ((1 : ℝ)), sq_nonneg ((x : ℝ)), mul_nonneg (show (0 : ℝ) ≤ 1 + x by linarith) (show (0 : ℝ) ≤ 1 + x by linarith)]
  specialize h1 n 
  simpa using h1