import Mathlib

open Real Set
open scoped Real

theorem inequalities_248660 (α β γ : ℝ) :
  min (min (sin α * cos β) (sin β * cos γ)) (sin γ * cos α) ≤ 1 / 2 := by

  by_contra h
  push_neg at h

  have h1 : sin α * cos β > 1 / 2 := by
    have h2 : min (min (sin α * cos β) (sin β * cos γ)) (sin γ * cos α) > 1 / 2 := h
    have h3 : min (min (sin α * cos β) (sin β * cos γ)) (sin γ * cos α) ≤ sin α * cos β := by
      simp [min_le_iff]
    linarith

  have h2 : sin β * cos γ > 1 / 2 := by
    have h4 : min (min (sin α * cos β) (sin β * cos γ)) (sin γ * cos α) > 1 / 2 := h
    have h5 : min (min (sin α * cos β) (sin β * cos γ)) (sin γ * cos α) ≤ sin β * cos γ := by
      have h6 : min (min (sin α * cos β) (sin β * cos γ)) (sin γ * cos α) ≤ min (sin α * cos β) (sin β * cos γ) := by
        apply min_le_left
      have h7 : min (sin α * cos β) (sin β * cos γ) ≤ sin β * cos γ := by
        apply min_le_right
      linarith
    linarith

  have h3 : sin γ * cos α > 1 / 2 := by
    have h4 : min (min (sin α * cos β) (sin β * cos γ)) (sin γ * cos α) > 1 / 2 := h
    have h5 : min (min (sin α * cos β) (sin β * cos γ)) (sin γ * cos α) ≤ sin γ * cos α := by
      apply min_le_right
    linarith

  have h4 : (sin α * cos β) + (sin β * cos γ) + (sin γ * cos α) > 3 / 2 := by 
    linarith

  have h5 : (sin α * cos β) + (sin β * cos γ) + (sin γ * cos α) ≤ 3 / 2 := by
    nlinarith [sq_nonneg (sin α - cos β), sq_nonneg (sin β - cos γ), sq_nonneg (sin γ - cos α),
      sq_nonneg (sin α - cos α), sq_nonneg (sin β - cos β), sq_nonneg (sin γ - cos γ),
        Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq γ]
  
  linarith