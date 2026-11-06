import Mathlib

open Real Set
open scoped Real

theorem calculus_16943 : cot (-π/3) = -sqrt 3 / 3 := by 
  rw [cot_eq_cos_div_sin]
  have h1 : cos (-π / 3) = 1 / 2 := by 
    have hcos : cos (-π / 3) = cos (π / 3) := by 
      rw [show -π / 3 = - (π / 3) by ring]
      rw [cos_neg]
    rw [hcos]
    exact Real.cos_pi_div_three
  have h2 : sin (-π / 3) = -sqrt 3 / 2 := by 
    have hsin : sin (-π / 3) = - sin (π / 3) := by 
      rw [show -π / 3 = - (π / 3) by ring]
      rw [sin_neg]
    rw [hsin]
    have hsin2 : sin (π / 3) = sqrt 3 / 2 := Real.sin_pi_div_three
    rw [hsin2]
    all_goals ring
  rw [h1, h2]
  field_simp
  <;> ring_nf 
  <;> field_simp 
  <;> ring