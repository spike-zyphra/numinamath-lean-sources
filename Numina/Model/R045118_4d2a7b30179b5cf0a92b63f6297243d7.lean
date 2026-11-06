import Mathlib

open Real

theorem inequalities_164514 (n : ℕ) (a : ℝ) (ha : -1 < a) :
    (1 + a) ^ n ≥ n * a + 1 := by
  have h1 : ∀ (n : ℕ), (1 + a) ^ n ≥ n * a + 1 := by 
    intro n 
    induction n with 
    | zero => 
      simp 
    | succ n ih => 
      simp [pow_succ] at ih ⊢
      nlinarith [sq_nonneg (a), sq_nonneg ((1 + a) ^ n - 1), mul_pos (show 0 < (1 + a) by linarith) (show 0 < (1 + a) by linarith), sq_nonneg (a - (-1)), pow_two_nonneg (a), pow_two_nonneg ((1 + a) ^ n - 1)]
  exact h1 n