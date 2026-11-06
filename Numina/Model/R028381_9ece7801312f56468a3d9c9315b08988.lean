import Mathlib

theorem algebra_107975 (α β γ : ℝ) (h₀ : Real.sin α + Real.sin β + Real.sin γ = 0) (h₁ : Real.cos α + Real.cos β + Real.cos γ = 0) :
    Real.cos α ^ 2 + Real.cos β ^ 2 + Real.cos γ ^ 2 = 3 / 2 := by
  have h2 : (Real.cos α + Real.cos β + Real.cos γ) ^ 2 + (Real.sin α + Real.sin β + Real.sin γ) ^ 2 = 0 := by
    rw [h₁, h₀]
    norm_num
  have h3 : Real.cos α ^ 2 + Real.cos β ^ 2 + Real.cos γ ^ 2 + 2 * (Real.cos α * Real.cos β + Real.cos α * Real.cos γ + Real.cos β * Real.cos γ) + (Real.sin α ^ 2 + Real.sin β ^ 2 + Real.sin γ ^ 2) + 2 * (Real.sin α * Real.sin β + Real.sin α * Real.sin γ + Real.sin β * Real.sin γ) = 0 := by
    have h4 : (Real.cos α + Real.cos β + Real.cos γ) ^ 2 + (Real.sin α + Real.sin β + Real.sin γ) ^ 2 = 0 := h2
    linarith [h4]

  have h4 : Real.cos γ = - (Real.cos α + Real.cos β) := by
    linarith [h₁]

  have h5 : Real.sin γ = - (Real.sin α + Real.sin β) := by
    linarith [h₀]

  have h6 : Real.cos γ ^ 2 + Real.sin γ ^ 2 = 1 := Real.cos_sq_add_sin_sq γ

  rw [h4, h5] at h6
  -- Now we have from previous derivation:
  -- (Real.cos α + Real.cos β) ^ 2 + (Real.sin α + Real.sin β) ^ 2 = 1
  -- Expand it:
  -- Real.cos α ^ 2 + Real.cos β ^ 2 + 2 * Real.cos α * Real.cos β + Real.sin α ^ 2 + Real.sin β ^ 2 + 2 * Real.sin α * Real.sin β = 1
  -- Simplify squares:
  -- (Real.cos α ^ 2 + Real.sin α ^ 2) + (Real.cos β ^ 2 + Real.sin β ^ 2) + 2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) =1
  -- Simplify to 1+1+ 2*(...) =1, leading to (...) = -1/2
  -- Now to compute the main goal.

  have h7 : Real.cos α ^ 2 + Real.cos β ^ 2 + Real.cos γ ^ 2 = 3 / 2 := by
    rw [show Real.cos γ = - (Real.cos α + Real.cos β) by linarith [h4]]
    nlinarith [Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.cos_sq_add_sin_sq γ, sq_nonneg (Real.cos α + Real.cos β), sq_nonneg (Real.sin α + Real.sin β)]

  linarith [h7]
  all_goals tauto