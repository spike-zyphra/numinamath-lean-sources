import Mathlib

open Real Set
open scoped Real

theorem calculus_17174 : sin (-π / 2) = -1 := by 
  have h1 : sin (-π / 2) = sin (- (π / 2)) := by ring_nf
  rw [h1]
  rw [sin_neg]
  have h2 : sin (π / 2) = 1 := Real.sin_pi_div_two
  simp [h2]
  <;> try linarith [Real.sin_pi_div_two]