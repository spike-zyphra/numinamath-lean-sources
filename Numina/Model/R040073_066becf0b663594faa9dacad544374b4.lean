import Mathlib

open Real

theorem calculus_131068 (f : ℝ → ℝ) (hf : f = fun x => (1 + 3 * x ^ 2) / (3 + x ^ 2)) (x0 : ℝ) (hx0 : x0 = 1) :
    Differentiable ℝ f ∧ deriv f x0 = 1 ∧ f x0 = x0 := by
  have h1 : Differentiable ℝ f := by
    rw [hf]
    apply Differentiable.div
    · -- Show that the numerator is differentiable
      apply Differentiable.add
      · -- Show that 1 is differentiable
        apply differentiable_const
      · -- Show that 3 * x^2 is differentiable
        apply Differentiable.mul
        · -- Show that 3 is differentiable
          apply differentiable_const
        · -- Show that x^2 is differentiable
          apply Differentiable.pow
          exact differentiable_id'
    · -- Show that the denominator is differentiable
      apply Differentiable.add
      · -- Show that 3 is differentiable
        apply differentiable_const
      · -- Show that x^2 is differentiable
        apply Differentiable.pow
        exact differentiable_id'
    · -- Show that the denominator is not zero
      intro x
      have h2 : (3 + x ^ 2 : ℝ) ≠ 0 := by
        have h3 : x ^ 2 ≥ 0 := sq_nonneg x
        linarith
      exact h2

  have h2 : deriv f x0 = 1 := by
    rw [hx0]
    rw [hf]
    simp [deriv_div, deriv_add, deriv_mul, deriv_pow, deriv_const, mul_comm]
    all_goals norm_num

  have h3 : f x0 = x0 := by
    rw [hx0]
    rw [hf]
    norm_num

  constructor
  · exact h1
  constructor
  · exact h2
  · exact h3