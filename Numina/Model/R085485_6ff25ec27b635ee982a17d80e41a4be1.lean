import Mathlib

theorem algebra_296945 (α : ℝ) (h₁ : Real.tan α > 1) (h₂ : Real.sin α + Real.cos α < 0) :
    Real.cos α < 0 := by
  have h3 : Real.cos α ≠ 0 := by
    by_contra h
    rw [Real.tan_eq_sin_div_cos, h] at h₁
    norm_num [h] at h₁
    all_goals linarith
  have h4 : Real.tan α = Real.sin α / Real.cos α := by
    rw [Real.tan_eq_sin_div_cos]
  rw [h4] at h₁
  by_cases h5 : Real.cos α > 0
  · -- Case cos α > 0
    have h6 : Real.sin α > Real.cos α := by
      have h7 : Real.sin α / Real.cos α > 1 := h₁
      apply (lt_div_iff₀ (by linarith [h5])).mp at h7
      linarith
    have h7 : Real.sin α > 0 := by linarith [h6, h5]
    have h8 : Real.sin α + Real.cos α > 0 := by linarith [h7, h5]
    linarith
  · -- cos α ≤ 0
    have h6 : Real.cos α ≤ 0 := by linarith
    have h7 : Real.cos α < 0 := by
      by_contra h
      push_neg at h
      have h8 : Real.cos α = 0 := by linarith [h6, h]
      contradiction
    exact h7