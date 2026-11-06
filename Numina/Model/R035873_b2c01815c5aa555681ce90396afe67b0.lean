import Mathlib

open Real Set
open scoped Real

theorem algebra_217921 {x : ℝ} (hx : cos x ≠ 0 ∧ sin x ≠ 0)
  (h : 1 / cos x - 1 / sin x = 2 * sqrt 6) :
  tan x + 1 / tan x = -4 ∨ tan x + 1 / tan x = 6 := by
  have h1 : sin x - cos x = 2 * sqrt 6 * sin x * cos x := by
    have hcos : cos x ≠ 0 := hx.1
    have hsin : sin x ≠ 0 := hx.2
    field_simp [hcos, hsin] at h ⊢
    linarith [h]
  
  have h2 : (sin x - cos x) ^ 2 = 24 * (sin x * cos x) ^ 2 := by
    calc
      (sin x - cos x) ^ 2 = (2 * sqrt 6 * sin x * cos x) ^ 2 := by rw [h1]
      _ = 4 * (sqrt 6) ^ 2 * (sin x * cos x) ^ 2 := by ring
      _ = 4 * 6 * (sin x * cos x) ^ 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
      _ = 24 * (sin x * cos x) ^ 2 := by ring
  
  have h3 : (sin x) ^ 2 + (cos x) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  
  have h4 : (sin x - cos x) ^ 2 = (sin x) ^ 2 + (cos x) ^ 2 - 2 * (sin x * cos x) := by
    ring
  
  have h5 : (sin x - cos x) ^ 2 = 1 - 2 * (sin x * cos x) := by
    rw [h4, h3]
    all_goals ring
  
  have h6 : 1 - 2 * (sin x * cos x) = 24 * (sin x * cos x) ^ 2 := by
    linarith [h2, h5]
  
  have h7 : 24 * (sin x * cos x) ^ 2 + 2 * (sin x * cos x) - 1 = 0 := by
    nlinarith [h6]
  
  have h8 : (sin x * cos x - 1 / 6) * (sin x * cos x + 1 / 4) = 0 := by
    nlinarith [h7]
  
  cases' (mul_eq_zero.mp h8) with h9 h10
  
  · -- Case where sin x * cos x = 1/6, thus tan x + cot x = 6
    have h11 : sin x * cos x = 1 / 6 := by
      linarith
    have htan : tan x + 1 / tan x = 6 := by
      have htan1 : tan x = sin x / cos x := by 
        rw [Real.tan_eq_sin_div_cos]
      have htan2 : sin x ^ 2 + cos x ^ 2 = 1 := by 
        linarith [Real.sin_sq_add_cos_sq x]
      field_simp [htan1, hx.1, hx.2]
      nlinarith [h11, htan2]
    
    right 
    exact htan
  
  · -- Case where sin x * cos x = -1/4, thus tan x + cot x = -4
    have h12 : sin x * cos x = -1 / 4 := by
      linarith
    have htan : tan x + 1 / tan x = -4 := by
      have htan1 : tan x = sin x / cos x := by 
        rw [Real.tan_eq_sin_div_cos]
      have htan2 : sin x ^ 2 + cos x ^ 2 = 1 := by 
        linarith [Real.sin_sq_add_cos_sq x]
      field_simp [htan1, hx.1, hx.2]
      nlinarith [h12, htan2]
    
    left 
    exact htan