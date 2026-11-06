import Mathlib

open Real Set
open scoped Real

theorem algebra_106061 {x : ℝ} (hx : x = π / 10) :
    sin (2 * x) * sin (3 * x) = cos (2 * x) * cos (3 * x) := by
  rw [hx]
  have h1 : 2 * (π / 10) = π / 5 := by ring
  have h2 : 3 * (π / 10) = 3 * π / 10 := by ring
  rw [h1, h2]
  -- rewrite to cos(A + B) = cos pi/2 = 0
  have h3 : cos (π / 5) * cos (3 * π / 10) - sin (π / 5) * sin (3 * π / 10) = 0 := by
    have h4 : cos (π / 5) * cos (3 * π / 10) - sin (π / 5) * sin (3 * π / 10) = cos (π / 5 + 3 * π / 10) := by
      rw [cos_add]
      all_goals ring
    rw [h4]
    have h5 : π / 5 + 3 * π / 10 = π / 2 := by ring
    rw [h5]
    have h6 : cos (π / 2) = 0 := by
      exact cos_pi_div_two
    linarith [h6]
  -- linarith goal to h1
  have h4 : sin (π / 5) * sin (3 * π / 10) - cos (π / 5) * cos (3 * π / 10) = 0 := by
    linarith [h3]
  linarith [h4]