import Mathlib

theorem calculus_156323 (F f : ℝ → ℝ)
    (hF : F = fun x => (1 / 2) * Real.sin (2 * x)) (hf : f = fun x => Real.cos (2 * x)) :
    Differentiable ℝ F ∧ ∀ x, deriv F x = f x := by
  constructor
  · -- Show that F is differentiable
    rw [hF]
    apply Differentiable.mul
    · -- Show that the constant 1/2 function is differentiable
      exact differentiable_const (1 / 2)
    · -- Show that sin(2x) is differentiable
      apply Differentiable.sin
      all_goals
      apply Differentiable.mul
      · -- Show that 2 is differentiable (constant)
        exact differentiable_const 2
      · -- Show that x is differentiable (identity)
        exact differentiable_id'
  · -- Show that the derivative of F equals f(x)
    intro x
    rw [hF, hf]
    simp [deriv_const_mul, deriv_id'', mul_comm]
    all_goals
      try ring_nf
      all_goals
        try simp [Real.sin_sq, Real.cos_sq]
        all_goals
          ring