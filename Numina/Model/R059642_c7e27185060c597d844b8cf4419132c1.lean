import Mathlib

open Real Set

theorem algebra_609787 (α β γ : ℝ)
    (h₀ : cos α + cos β + cos γ = 1) (h₁ : sin α + sin β + sin γ = 1) :
    cos α ≥ (-1 - sqrt 7) / 4 := by
  have h2 : cos β + cos γ = 1 - cos α := by linarith
  have h3 : sin β + sin γ = 1 - sin α := by linarith
  have h4 : (cos β + cos γ) ^ 2 + (sin β + sin γ) ^ 2 = 2 + 2 * cos (β - γ) := by
    rw [cos_sub]
    have h5 : (cos β + cos γ) ^ 2 + (sin β + sin γ) ^ 2 =
          (cos β ^ 2 + sin β ^ 2) + (cos γ ^ 2 + sin γ ^ 2) + 2 * (cos β * cos γ + sin β * sin γ) := by ring
    rw [h5]
    have h6 : cos β ^ 2 + sin β ^ 2 = 1 := by exact Real.cos_sq_add_sin_sq β
    have h7 : cos γ ^ 2 + sin γ ^ 2 = 1 := by exact Real.cos_sq_add_sin_sq γ
    rw [h6, h7]
    nlinarith [Real.cos_sq_add_sin_sq β, Real.cos_sq_add_sin_sq γ, Real.cos_sq_add_sin_sq (β - γ)]
  rw [h2, h3] at h4
  have h5 : (1 - cos α) ^ 2 + (1 - sin α) ^ 2 = 2 + 2 * cos (β - γ) := by linarith
  have h8 : cos (β - γ) ≤ 1 := by 
    apply Real.cos_le_one
  have h9 : cos α + sin α ≥ -1 / 2 := by 
    nlinarith [h5, h8, Real.cos_sq_add_sin_sq α, sq_nonneg (β - γ), sq_nonneg (cos β - cos γ), sq_nonneg (sin β - sin γ)]
  have h10 : sin α ≥ -1/2 - cos α := by nlinarith
  have h11 : cos α ^ 2 + sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  nlinarith [h11, h10, Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ 7 by norm_num), sq_nonneg (cos α - (-1 - sqrt 7) / 4), sq_nonneg (sin α - (-1 + sqrt 7) / 4)]