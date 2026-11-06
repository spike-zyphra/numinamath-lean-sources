import Mathlib

theorem algebra_7016 (n : ℕ) (θ : ℝ) (hn : n > 0) :
    (Real.exp (I * θ))^n = Real.exp (I * n * θ) := by
  induction n with
  | zero => 
    exfalso
    linarith
  | succ k ih =>
    cases k with
    | zero => 
      simp [Real.exp_add]
    | succ k =>
      simp [pow_succ, ih] at *
      <;> simp [Real.exp_add, mul_add, add_mul]
      <;> ring_nf <;> norm_num