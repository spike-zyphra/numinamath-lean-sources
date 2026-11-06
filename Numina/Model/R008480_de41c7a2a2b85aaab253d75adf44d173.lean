import Mathlib

open Polynomial

theorem algebra_10345 (b c : ℝ) (h : (X ^ 2 + C (-20) * X + C 36 : ℝ[X]) = (X + C b) ^ 2 + C c) :
    b + c = -74 := by

  have h1 := congr_arg (fun f => f.eval 0) h
  have h2 := congr_arg (fun f => f.eval 1) h
  have h3 := congr_arg (fun f => f.eval 2) h
  simp at h1 h2 h3
  
  have h4 : b = -10 := by
    nlinarith
  
  have h5 : c = -64 := by
    rw [h4] at h1
    nlinarith
  
  rw [h4, h5]
  norm_num