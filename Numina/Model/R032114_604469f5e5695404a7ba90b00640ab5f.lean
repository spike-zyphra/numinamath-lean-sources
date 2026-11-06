import Mathlib

theorem inequalities_180778 (x : ℝ) (hx : -1 ≤ x) (n : ℕ) :
    (1 + x) ^ n ≥ 1 + n * x := by 
  have h1 : ∀ (n : ℕ), (1 + x) ^ n ≥ 1 + (n : ℝ) * x := by 
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      simp [pow_succ, mul_add, add_mul] at ih ⊢
      nlinarith [sq_nonneg (x), sq_nonneg ((1 : ℝ) + x), sq_nonneg (x * (n : ℝ)), mul_nonneg (show (0 : ℝ) ≤ (1 + x) by linarith) (show (0 : ℝ) ≤ (1 + x) by linarith), mul_nonneg (show (0 : ℝ) ≤ (x + 1) by linarith) (show (0 : ℝ) ≤ (x + 1) by linarith), sq_nonneg (x - 0)]
  specialize h1 n
  simpa using h1