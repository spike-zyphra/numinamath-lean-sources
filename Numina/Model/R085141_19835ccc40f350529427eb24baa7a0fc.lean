import Mathlib

open Matrix

theorem calculus_22361 (a : ℝ) :
    !![3*a^2-3, 3*a; 2*a^2-a-2, 2*a-1] *
    !![-1, -3*a-2; a, 3*a^2+2*a-3] =
    !![3, 6; 2, 7] := by
  ring_nf
  <;> simp [mul_apply, add_mul, mul_add]
  <;> ring