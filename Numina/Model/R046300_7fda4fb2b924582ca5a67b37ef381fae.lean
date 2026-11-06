import Mathlib

open Real Set

theorem algebra_130380 {x : ℝ} :
  arcsin (cos (arcsin x)) + arccos (sin (arccos x)) = π / 2
:= by
  have h1 : cos (arcsin x) = Real.sqrt (1 - x ^ 2) := by
    rw [cos_arcsin]
  have h2 : sin (arccos x) = Real.sqrt (1 - x ^ 2) := by
    rw [sin_arccos]
  rw [h1, h2]
  have h3 : arcsin (Real.sqrt (1 - x ^ 2)) + arccos (Real.sqrt (1 - x ^ 2)) = π / 2 := by
    have h4 : arcsin (Real.sqrt (1 - x ^ 2)) + arccos (Real.sqrt (1 - x ^ 2)) = π / 2 := by
      rw [Real.arccos_eq_pi_div_two_sub_arcsin]
      ring
    exact h4
  exact h3