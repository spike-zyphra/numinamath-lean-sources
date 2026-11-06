import Mathlib
open Nat Real

theorem calculus_4698 (x y : ℝ) (h₀ : Real.tan x + Real.tan y = 4) (h₁ : 1 / Real.tan x + 1 / Real.tan y = 5) :
    Real.tan (x + y) = 20 := by
  have h2 : Real.tan x ≠ 0 := by
    by_contra h
    have h3 : Real.tan y = 4 := by linarith [h₀, h]
    have h4 : 1 / Real.tan x + 1 / Real.tan y = 5 := h₁
    simp [h, h3] at h4
    all_goals linarith
  have h3 : Real.tan y ≠ 0 := by
    by_contra h
    have h4 : Real.tan x = 4 := by linarith [h₀, h]
    have h5 : 1 / Real.tan x + 1 / Real.tan y = 5 := h₁
    simp [h4, h] at h5
    all_goals linarith
  have h4 : Real.tan x * Real.tan y = 4 / 5 := by
    have h5 : 1 / Real.tan x + 1 / Real.tan y = 5 := h₁
    have h6 : Real.tan x + Real.tan y = 4 := h₀
    have h7 : Real.tan x ≠ 0 := h2
    have h8 : Real.tan y ≠ 0 := h3
    field_simp [h7, h8] at h5
    nlinarith [h6]
  have h5 : Real.tan (x + y) = (Real.tan x + Real.tan y) / (1 - Real.tan x * Real.tan y) := by
    have htan1 : Real.tan (x + y) = Real.sin (x + y) / Real.cos (x + y) := by
      rw [Real.tan_eq_sin_div_cos]
    have htan2 : (Real.tan x + Real.tan y) / (1 - Real.tan x * Real.tan y) = (Real.sin x / Real.cos x + Real.sin y / Real.cos y) / (1 - (Real.sin x / Real.cos x) * (Real.sin y / Real.cos y)) := by
      simp [Real.tan_eq_sin_div_cos]
    have htan3 : Real.cos x ≠ 0 := by
      by_contra h
      have htan0 : Real.tan x = 0 := by
        rw [Real.tan_eq_sin_div_cos]
        simp [h]
      contradiction
    have htan4 : Real.cos y ≠ 0 := by
      by_contra h
      have htan0 : Real.tan y = 0 := by
        rw [Real.tan_eq_sin_div_cos]
        simp [h]
      contradiction
    have htan5 : Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
      rw [Real.sin_add]
    have htan6 : Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := by
      rw [Real.cos_add]
    rw [htan1, htan2, htan5, htan6]
    field_simp [htan3, htan4]
    <;> ring
  rw [h5, h₀, h4]
  norm_num