import Mathlib

open Real

theorem calculus_178264 (f : ℝ → ℝ) (hf : f = fun x => x^2 - 2 * x + 3) :
    Differentiable ℝ f ∧ ∀ x, deriv f x = 2 * x - 2 ∧ iteratedDeriv 2 f x = 2 ∧ iteratedDeriv 3 f x = 0 := by
  constructor
  · -- Show that f is differentiable
    rw [hf]
    all_goals
      fun_prop
  · -- Show the first three differentials
    intro x
    constructor
    · -- First derivative
      rw [hf]
      simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    constructor
    · -- Second derivative
      have h1 : deriv f = fun y => 2 * y - 2 := by
        funext y
        rw [hf]
        simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
      simp [iteratedDeriv_succ, h1]
      all_goals
        try { simp [deriv_sub, deriv_add, deriv_pow, deriv_const, mul_comm] }
    · -- Third derivative
      have h1 : deriv f = fun y => 2 * y - 2 := by
        funext y
        rw [hf]
        simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
      have h2 : deriv (deriv f) = fun y => 2 := by
        rw [h1]
        funext y
        simp [deriv_sub, deriv_add, deriv_pow, deriv_const, mul_comm]
      simp [iteratedDeriv_succ, h2]
      all_goals
        try { simp [deriv_const]  }