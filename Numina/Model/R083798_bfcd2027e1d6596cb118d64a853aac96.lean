import Mathlib

open Real Set
open scoped Real

theorem calculus_16473 (θ : ℝ) (h : cos θ + sin θ = 5 / 4) :
    sin (2 * θ) = 9 / 16 := by 
  have h1 : sin (2 * θ) = 2 * sin θ * cos θ := by 
    rw [sin_two_mul]
  
  have h2 : (cos θ + sin θ) ^ 2 = (5 / 4) ^ 2 := by 
    rw [h]

  have h3 : (cos θ + sin θ) ^ 2 = cos θ ^ 2 + sin θ ^ 2 + 2 * (sin θ * cos θ) := by 
    ring
  
  rw [h3] at h2
  
  have h4 : cos θ ^ 2 + sin θ ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq θ
  
  rw [h4] at h2
  
  norm_num at h2
  
  have h5 : 2 * (sin θ * cos θ) = 9 / 16 := by 
    linarith
  
  rw [h1]
  linarith [h5]