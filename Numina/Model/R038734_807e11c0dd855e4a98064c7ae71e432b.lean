import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_249394 (a b c d : ℝ) (f : ℝ → ℝ) (hpos : ∀ x, f x > 0)
    (hf : f = λ x => 1 + a * cos x + b * sin x + c * cos (2 * x) + d * sin (2 * x)) : ∀ x, f x < 3 := by 
  intro x

  -- We write some basic trigonometric identities
  have eq_1 : cos x = - cos (x + 2 * (π / 3)) - cos (x - 2 * (π / 3)) := by
    rw [cos_add, cos_sub, cos_two_mul, sin_two_mul, cos_pi_div_three, sin_pi_div_three]
    ring_nf

  have eq_2 : sin x = - sin (x + 2 * (π / 3)) - sin (x - 2 * (π / 3)) := by
    rw [sin_add, sin_sub, cos_two_mul, sin_two_mul, cos_pi_div_three, sin_pi_div_three]
    ring_nf

  have eq_3 : cos (2 * x) = - cos (2 * (x + 2 * (π / 3))) - cos (2 * (x - 2 * (π / 3))) := by
    rw [mul_add, mul_sub, cos_add, cos_sub, cos_two_mul (2 * (π / 3)), sin_two_mul (2 * (π / 3)), cos_two_mul (π / 3), sin_two_mul (π / 3), cos_pi_div_three, sin_pi_div_three]
    ring_nf

  have eq_4 : sin (2 * x) = - sin (2 * (x + 2 * (π / 3))) - sin (2 * (x - 2 * (π / 3))) := by
    rw [mul_add, mul_sub, sin_add, sin_sub, cos_two_mul (2 * (π / 3)), sin_two_mul (2 * (π / 3)), cos_two_mul (π / 3), sin_two_mul (π / 3), cos_pi_div_three, sin_pi_div_three]
    ring_nf

  -- We write the sum of f applied to x, x + 2π/3 and x - 2π/3, and show that it is equal to 3 by using the identities
  have : (f x) + f (x + 2 * (π / 3)) + f (x - 2 * (π / 3)) = 3 := by 
    simp only [hf]
    rw [eq_1, eq_2, eq_3, eq_4]
    ring_nf
    <;> simp [cos_two_mul, sin_two_mul]

  have hx1 : f x > 0 := hpos x
  have hx2 : f (x + 2 * (π / 3)) > 0 := hpos (x + 2 * (π / 3))
  have hx3 : f (x - 2 * (π / 3)) > 0 := hpos (x - 2 * (π / 3))

  linarith