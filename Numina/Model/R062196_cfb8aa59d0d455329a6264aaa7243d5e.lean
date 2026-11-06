import Mathlib

open Real Set
open scoped Real

theorem algebra_4812 (x : Real) (hx : x ∈ Ioo 0 (π / 2)) (h : sin x = 5 / 13) :
    5 / tan x + 24 / cos x = 38 := by 
  have h1 : 0 < x := hx.left
  have h2 : x < π / 2 := hx.right
  
  have hcos_pos : cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]

  have hcos_sq : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
  
  rw [h] at hcos_sq
  
  have hcos_sq2 : cos x ^ 2 = 1 - (5 / 13) ^ 2 := by linarith
  
  have hcos_sq3 : cos x ^ 2 = 144 / 169 := by 
    rw [hcos_sq2]
    norm_num
  
  have hcos : cos x = 12 / 13 := by
    nlinarith [hcos_sq3, hcos_pos]

  have htan : tan x = 5 / 12 := by
    rw [tan_eq_sin_div_cos, h, hcos]
    all_goals norm_num
  
  rw [htan, hcos]
  norm_num [h]