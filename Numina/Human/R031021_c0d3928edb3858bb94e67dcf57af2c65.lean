import Mathlib

open Real

theorem algebra_425452 : tan (-23 * π / 3) = √3 := by

  have h1: tan (-23 * π / 3) = tan (π / 3) := by
    have: π / 3 = -23 * π / 3 + ↑(8:ℤ) * π := by ring
    rw [this, tan_add_int_mul_pi]

  have h2: tan (π / 3) = √3 := tan_pi_div_three

  rw [h1, h2]