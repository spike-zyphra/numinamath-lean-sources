import Mathlib

open Real Set
open scoped BigOperators

/-Show that the function y=tanx does not have a derivative at the point x=π/2.-/
theorem calculus_155288 : ¬ DifferentiableAt ℝ tan (π/2) := by

  -- Assume for contradiction that tan is differentiable at π/2
  intro h
  -- Using Lean's library, we know that if tan is differentiable at x, then cos(x) ≠ 0
  have h1 : cos (π / 2) ≠ 0 := by
    have h2 : DifferentiableAt ℝ tan (π / 2) := h
    have h3 := Real.differentiableAt_tan.mp h2
    exact h3
  -- But we know from standard real analysis that cos(π/2) = 0
  have h2 : cos (π / 2) = 0 := Real.cos_pi_div_two
  -- Thus we have a contradiction
  contradiction
