import Mathlib

open Real Set
open scoped Real

theorem algebra_13318 (x : ℝ) (hx : x ∈ Ioo 0 (π / 2)) (h : tan x = 8 / 15) :
    (sin x ^ 2 - 2 * sin x * cos x + cos x ^ 2) / (sin x ^ 2 - cos x ^ 2) = -7 / 23 := by 
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have h3 : sin x / cos x = 8 / 15 := by
    have htan : tan x = sin x / cos x := by
      rw [tan_eq_sin_div_cos]
    rw [htan] at h 
    linarith
  have h4 : sin x = 8 / 15 * cos x := by 
    have h5 : cos x ≠ 0 := by linarith
    field_simp [h5] at h3 ⊢
    linarith 
  have h6 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
  have h5 : cos x ^ 2 = 225 / 289 := by 
    rw [h4] at h6 
    nlinarith 
  have h7 : cos x = 15 / 17 := by
    nlinarith [h5, h2]
  have h8 : sin x = 8 / 17 := by 
    rw [h7] at h4 
    linarith 
  have h9 : sin x ^ 2 - 2 * sin x * cos x + cos x ^ 2 = 49 / 289 := by
    rw [h8, h7]
    norm_num 
  have h10 : sin x ^ 2 - cos x ^ 2 = -161 / 289 := by 
    rw [h8, h7]
    norm_num 
  rw [h9, h10]
  norm_num