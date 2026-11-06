import Mathlib

open Real Set

theorem algebra_225510 {x : ℝ} (hx : x ∈ Icc (-1) 1) :
  arcsin (cos (arcsin x)) = π / 2 - arccos (sin (arccos x)) := by

  rw [cos_arcsin, sin_arccos, arcsin_eq_pi_div_two_sub_arccos]