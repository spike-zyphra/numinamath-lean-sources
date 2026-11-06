import Mathlib

open Real Set
open scoped Real

theorem calculus_22530 : cot (3 * π / 2) = 0 := by
  have h1 : cos (3 * π / 2) = 0 := by
    have h2 : 3 * π / 2 = π + π / 2 := by ring
    rw [h2]
    rw [cos_add, cos_pi, sin_pi]
    norm_num
  have h3 : sin (3 * π / 2) = -1 := by
    have h4 : 3 * π / 2 = π + π / 2 := by ring
    rw [h4]
    rw [sin_add, cos_pi, sin_pi]
    norm_num
  rw [cot_eq_cos_div_sin]
  rw [h1, h3]
  norm_num