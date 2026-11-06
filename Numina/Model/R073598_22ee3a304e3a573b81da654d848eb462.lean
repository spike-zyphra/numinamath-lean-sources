import Mathlib

open Real Set
open scoped Real

theorem algebra_247354 (b c : ℝ) :
  (1 - cos b * cos c) ^ 2 - 2 * (1 - cos b * cos c) - sin b ^ 2 * sin c ^ 2 + sin b ^ 2 + sin c ^ 2 = 0 := by 
  have h1 : cos b ^ 2 + sin b ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq b
  have h2 : cos c ^ 2 + sin c ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq c
  
  nlinarith [sq_nonneg (sin b - sin c), sq_nonneg (cos b - cos c), sq_nonneg (sin b + sin c), sq_nonneg (cos b + cos c), h1, h2]