import Mathlib

theorem algebra_16647 {x y : ℝ}  (h₀ : Real.tan x + Real.tan y = 25) (h₁ : 1 / Real.tan x + 1 / Real.tan y = 30) :
Real.tan (x + y) = 150 := by
  have h2 : Real.tan x ≠ 0 := by
    by_contra h
    have h3 : Real.tan x + Real.tan y = 25 := h₀
    rw [h] at h3
    have h4 : Real.tan y = 25 := by linarith
    rw [h] at h₁
    field_simp [h4] at h₁
    all_goals linarith
  have h3 : Real.tan y ≠ 0 := by
    by_contra h
    have h4 : Real.tan x + Real.tan y = 25 := h₀
    rw [h] at h4
    have h5 : Real.tan x = 25 := by linarith
    rw [h] at h₁
    field_simp [h5] at h₁
    all_goals linarith
  have eq1 : Real.tan x * Real.tan y = 5 / 6 := by
    have h4 : Real.tan x ≠ 0 := h2
    have h5 : Real.tan y ≠ 0 := h3
    have eq2 : 1 / Real.tan x + 1 / Real.tan y = (Real.tan x + Real.tan y) / (Real.tan x * Real.tan y) := by
      field_simp [h4, h5]
      <;> ring
    rw [eq2] at h₁
    have h6 : Real.tan x + Real.tan y = 25 := h₀
    rw [h6] at h₁
    field_simp at h₁ ⊢
    nlinarith
  have eq2 : Real.tan (x + y) = (Real.tan x + Real.tan y) / (1 - Real.tan x * Real.tan y) := by 
    have h2' : Real.tan (x + y) = Real.sin (x + y) / Real.cos (x + y) := by 
      rw [Real.tan_eq_sin_div_cos]
    rw [h2']
    rw [Real.sin_add, Real.cos_add]
    rw [show Real.tan x = Real.sin x / Real.cos x by rw [Real.tan_eq_sin_div_cos], 
        show Real.tan y = Real.sin y / Real.cos y by rw [Real.tan_eq_sin_div_cos]]
    have h2'' : Real.cos x ≠ 0 := by 
      by_contra h4
      have he1 : Real.tan x = 0 := by 
        rw [show Real.tan x = Real.sin x / Real.cos x by rw [Real.tan_eq_sin_div_cos]]
        rw [h4]
        norm_num
      have he2 : Real.tan x ≠ 0 := h2
      contradiction
    have h3'' : Real.cos y ≠ 0 := by 
      by_contra h4
      have he2 : Real.tan y = 0 := by 
        rw [show Real.tan y = Real.sin y / Real.cos y by rw [Real.tan_eq_sin_div_cos]]
        rw [h4]
        norm_num
      have he3 : Real.tan y ≠ 0 := h3
      contradiction
    field_simp [h2'', h3'']
    ring
  rw [eq2]
  rw [show Real.tan x + Real.tan y = 25 by linarith, show Real.tan x * Real.tan y = 5 / 6 by linarith [eq1]]
  all_goals norm_num