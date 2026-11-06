import Mathlib

open Real Set
open scoped Real

theorem calculus_11557 (x : ℝ) (hx : x = -sqrt 3 / 2) :
    arcsin x = -π / 3 := by
  rw [hx]
  have h3 : (-sqrt 3 / 2 : ℝ) = sin (-π / 3) := by
    rw [show sin (-π / 3) = sin (-(π / 3)) by ring]
    rw [sin_neg]
    have h4 : sin (π / 3) = sqrt 3 / 2 := sin_pi_div_three
    rw [h4]
    ring
  rw [h3]
  have h5 : -(Real.pi / 2) ≤ (-Real.pi / 3 : ℝ) := by
    linarith [Real.pi_pos]
  have h6 : (-Real.pi / 3 : ℝ) ≤ Real.pi / 2 := by
    linarith [Real.pi_pos]
  have h7 : arcsin (sin (-Real.pi / 3)) = -Real.pi / 3 := by
    apply arcsin_sin
    all_goals 
      linarith [Real.pi_pos]
  rw [h7]
  all_goals ring_nf <;> linarith [Real.pi_pos]