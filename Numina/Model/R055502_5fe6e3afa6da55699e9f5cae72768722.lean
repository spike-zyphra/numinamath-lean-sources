import Mathlib

open Real Set
open scoped Real

theorem calculus_12915 : tan (9 * π / 4) = 1 := by
  have h1 : 9 * π / 4 = π / 4 + 2 * π := by
    linarith [Real.pi_pos]
  rw [h1]
  have h2 : tan (π / 4 + 2 * π) = tan (π / 4) := by
    have htan : tan (π / 4 + 2 * π) = tan (π / 4 + π + π) := by ring_nf
    rw [htan]
    rw [Real.tan_add_pi]
    rw [Real.tan_add_pi]
  rw [h2]
  exact Real.tan_pi_div_four