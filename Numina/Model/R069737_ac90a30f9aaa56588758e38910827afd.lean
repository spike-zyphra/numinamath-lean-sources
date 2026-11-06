import Mathlib

open Real

theorem inequalities_224818 (n : ℕ) (hn : n > 0) (x : ℝ) (hx : -1 < x) :
    (1 + x) ^ n ≥ 1 + n * x := by 
  induction n with 
  | zero => 
    linarith
  | succ m ih =>
    cases m with 
    | zero =>
      simp
    | succ m =>
      simp [pow_succ, mul_add, add_mul, pow_succ] at ih ⊢
      nlinarith [sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1), ih, mul_nonneg (show (0 : ℝ) ≤ (1 + x) by linarith) (show (0 : ℝ) ≤ (1 + x) by linarith)]