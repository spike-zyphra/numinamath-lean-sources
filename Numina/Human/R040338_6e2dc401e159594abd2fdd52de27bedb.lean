import Mathlib

open Real Set
open scoped Real

theorem calculus_23401 : arccos (-1 / sqrt 2) = 3 * π / 4 := by
  have h1 : cos (3 * π / 4) = -1 / sqrt 2 := by
    have h1 : cos (3 * π / 4) = -sqrt 2 / 2 := by
      have h1 : 3 * π / 4 = π - (π / 4) := by ring
      rw [h1]
      rw [cos_pi_sub]
      have h2 : cos (π / 4) = sqrt 2 / 2 := by
        exact Real.cos_pi_div_four
      rw [h2]
      ring
    rw [h1]
    field_simp
  have h2 : 0 ≤ 3 * π / 4 := by
    have h2 : 0 ≤ π := Real.pi_nonneg
    linarith [h2]
  have h3 : 3 * π / 4 ≤ π := by
    have h3 : π > 0 := Real.pi_pos
    linarith [h3]
  rw [←h1]
  apply arccos_cos h2 h3