import Mathlib

open Real
open scoped BigOperators

theorem inequalities_271956 (x : ℝ) (hx : -1 < x ∧ x ≠ 0) (n : ℕ) (hn : 0 < n) :
    (1 + x)^n ≥ n * x := by
  have h1 : (1 + x) ^ n ≥ 1 + ↑n * x := by
    have h3 : -1 < x := hx.1
    have h4 : (1 + x) ^ n ≥ 1 + ↑n * x := by
      have h5 : ∀ (n : ℕ), (1 + x) ^ n ≥ 1 + ↑n * x := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          simp [pow_succ] at ih ⊢
          nlinarith [sq_nonneg (x), sq_nonneg ((1 + x)), ih, show (1 + x) > 0 by linarith, show (x + 1) * (x + 1) ≥ 0 by nlinarith]
      specialize h5 n
      simpa using h5
    linarith
  have h2 : (1 + ↑n * x) ≥ (n * x : ℝ) := by
    have h4 : (1 : ℝ) ≥ 0 := by norm_num
    have h5 : (1 + ↑n * x : ℝ) ≥ (n * x : ℝ) := by
      nlinarith
    linarith
  linarith