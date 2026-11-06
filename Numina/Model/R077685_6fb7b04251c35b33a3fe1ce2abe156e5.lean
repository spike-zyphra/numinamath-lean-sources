import Mathlib

open Real Set
open scoped Real

theorem algebra_304851 {x : ℝ} (hx : x = 18 * π / 180) :
    sin (2 * x) * sin (3 * x) = cos (2 * x) * cos (3 * x) := by 
  rw [hx]
  have h1 : 2 * (18 * π / 180 : ℝ) = Real.pi / 5 := by 
    ring_nf
  have h2 : 3 * (18 * π / 180 : ℝ) = 3 * Real.pi / 10 := by 
    ring_nf
  rw [h1, h2]
  have h3 : cos (Real.pi / 5) * cos (3 * Real.pi / 10) - sin (Real.pi / 5) * sin (3 * Real.pi / 10) = 0 := by
    have h4 : cos (Real.pi / 5) * cos (3 * Real.pi / 10) - sin (Real.pi / 5) * sin (3 * Real.pi / 10) = cos (Real.pi / 5 + 3 * Real.pi / 10) := by
      rw [cos_add]
      <;> ring_nf
    rw [h4]
    have h5 : Real.pi / 5 + 3 * Real.pi / 10 = Real.pi / 2 := by 
      linarith [Real.pi_pos]
    rw [h5]
    have h6 : cos (Real.pi / 2) = 0 := by
      exact cos_pi_div_two
    rw [h6]
    all_goals linarith
  linarith [h3]