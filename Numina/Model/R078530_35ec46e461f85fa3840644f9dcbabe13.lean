import Mathlib

open Real

theorem inequalities_148032 (x : ℝ) (hx : x ≥ -1) (n : ℕ) (hn : n ≥ 1) :
    (1 + x) ^ n ≥ 1 + n * x := by 
  induction n with 
  | zero => 
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero =>
      simp
    | succ n =>
      simp [pow_succ, pow_succ] at ih ⊢
      nlinarith [sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x - (n + 1 : ℝ)), sq_nonneg (x + (n + 1 : ℝ)), ih, mul_self_nonneg (x : ℝ), mul_self_nonneg (x - 1 : ℝ), mul_self_nonneg (x + 1 : ℝ)]