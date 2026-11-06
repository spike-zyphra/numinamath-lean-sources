import Mathlib

open Real Set
open scoped Real

theorem calculus_14442 {x : ℝ} (h : sin x = 3 * cos x) : sin x * cos x = 3 / 10 := by 
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq x
  have h2 : sin x = 3 * cos x := h
  rw [h2] at h1 
  have h3 : (3 * cos x) ^ 2 + cos x ^ 2 = 1 := h1
  have h4 : 9 * cos x ^ 2 + cos x ^ 2 = 1 := by
    nlinarith
  have h5 : 10 * cos x ^ 2 = 1 := by
    nlinarith
  have h6 : cos x ^ 2 = 1 / 10 := by 
    nlinarith 
  have h7 : sin x * cos x = 3 * cos x ^ 2 := by 
    rw [h2]
    all_goals ring 
  rw [h7]
  rw [h6]
  all_goals norm_num 
  all_goals ring 
  all_goals nlinarith 
  all_goals norm_num
  all_goals nlinarith