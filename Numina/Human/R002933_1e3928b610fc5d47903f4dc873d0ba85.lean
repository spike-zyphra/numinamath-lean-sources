import Mathlib

/- IMO 1959 Problem A3 Let a, b, c be real numbers. Given the equation for cos x: a cos 2 x + b cos x + c = 0, form a quadratic equation in cos 2x whose roots are the same values of x. Compare the equations in cos x and cos 2x for a=4, b=2, c=-1. -/
theorem algebra_131959 (a b c x : ℝ)
  (h : a * (Real.cos x)^2 + b * Real.cos x + c = 0) :
  a^2 * (Real.cos (2 * x))^2 + (2 * a^2 + 4 * a * c - 2 * b^2) * Real.cos (2 * x) + (4 * c^2 + 4 * a * c - 2 * b^2 + a^2) = 0 := by
  -- use the double angle formula and factorise
  trans 4 * (a * (Real.cos x)^2 + b * Real.cos x + c) * (a * (Real.cos x)^2 - b * Real.cos x + c)
  · rw [Real.cos_two_mul]
    ring
  -- conclude
  rw [h]
  ring