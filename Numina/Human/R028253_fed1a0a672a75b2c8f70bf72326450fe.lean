import Mathlib

open Real Set
open scoped BigOperators

/- The monotonic increasing interval of the function $f(x)=2x-\ln x$ is __________.-/
theorem algebra_9390 {f : ℝ → ℝ} (hf : f = λ x => 2 * x - log x) :
    MonotoneOn f (Ioi (1 / 2)) := by
  -- We prove that $f(x)$ is monotone on $(1/2,+\infty)$ by calculating its deriv.
  apply monotoneOn_of_deriv_nonneg
  -- $(1/2,+\infty)$ is convex.
  . exact convex_Ioi (1 / 2)
  -- $f(x)$ is continuous on $(1/2,+\infty)$.
  . rw [hf]
    apply ContinuousOn.sub (f := fun x => 2 * x)
    . apply ContinuousOn.mul
      . exact continuousOn_const
      exact continuousOn_id' (Ioi (1 / 2))
    . intro x hx
      apply ContinuousWithinAt.log
      . apply continuousWithinAt_id
      exact fun h => by norm_num [h] at hx
  -- $f(x)$ is differentaible on $(1/2,+\infty)$.
  . rw [hf]
    apply DifferentiableOn.sub (f := fun x => 2 * x)
    . apply DifferentiableOn.mul
      . exact differentiableOn_const 2
      exact differentiableOn_id'
    intro x hx
    apply DifferentiableWithinAt.log
    . apply differentiableWithinAt_id
    exact fun h => by norm_num [h] at hx
  -- Deriv of $f(x)$ is nonneg on $(1/2,+\infty)$.
  intro x hx
  rw [hf, deriv_sub (f := fun x => 2 * x), deriv_mul]
  simp at hx ⊢
  have := mul_lt_mul_of_pos_left hx (show 0 < x⁻¹ by positivity)
  rw [inv_mul_cancel₀ (by positivity)] at this
  field_simp at this
  have := mul_lt_mul_of_pos_left this (show (0 : ℝ) < 2 by norm_num)
  simp at this
  linarith
  . exact differentiableAt_const 2
  . exact differentiableAt_id'
  . apply DifferentiableAt.mul
    . exact differentiableAt_const 2
    exact differentiableAt_id'
  . apply DifferentiableAt.log
    . exact differentiableAt_id'
    exact fun h => by norm_num [h] at hx
