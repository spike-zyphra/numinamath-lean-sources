import Mathlib

open Real Set
open scoped Real

/- Simplify
\[4 \sin x \sin (60^\circ - x) \sin (60^\circ + x).\]The answer will be a trigonometric function of some simple function of $x,$ like "$\cos (2x)$" or "$\sin (x^3)$". -/
theorem calculus_22272 : 4 * sin x * sin (π/3 - x) * sin (π/3 + x) = sin (3 * x) := by
  -- first, we prove a product-to-sum equation.
  have pro_sum_sin(a b:ℝ): (sin a) * (sin b) =
    (cos (a-b) - cos (a+b)) / 2 := by
    rw [cos_sub, cos_add]; simp
  -- then we can simplify sin(π /3 - x) sin (π /3 + x)
  have h1: sin (π/3 - x) * sin (π/3 + x) =
    (cos (2*x) + 1/2) /2 := by
    rw [pro_sum_sin]
    have hh1: π/3 - x - (π/3+x) = -(2*x) := by ring
    have hh2: π/3-x + (π/3+x) = π-π/3 := by ring
    rw [hh1, hh2]
    rw [cos_neg, cos_pi_sub, cos_pi_div_three]; simp
  -- substitute back and simplify
  have h2: 4 * sin x * sin (π/3 - x) * sin (π/3 + x) =
    2*(sin x * cos (2*x)) + sin x := by
    rw [mul_assoc, h1]
    ring
  -- again, by product-to-sum, sinx cos2x = sin3x + sin-x
  have pro_sum_sincos(a b:ℝ): sin a * cos b = (sin (a+b) + sin (a-b))/2
    := by
    rw [sin_add, sin_sub]
    ring
  have h3: 2*(sin x * cos (2*x)) = sin (3*x) - sin x := by
    rw [pro_sum_sincos]
    have hh1: x+2*x = 3*x := by ring
    have hh2: x-2*x = -x := by ring
    rw [hh1, hh2, sin_neg]
    ring
  -- so the expression simplifies to sin3x
  rw [h2, h3]; ring