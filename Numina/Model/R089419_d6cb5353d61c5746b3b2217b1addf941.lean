import Mathlib

theorem algebra_173244 (α β γ : ℝ)
    (h₀ : Real.cos α + Real.cos β + Real.cos γ = Real.sqrt (1 / 5))
    (h₁ : Real.sin α + Real.sin β + Real.sin γ = Real.sqrt (4 / 5)) :
    Real.cos (α - β) + Real.cos (β - γ) + Real.cos (γ - α) = -1 := by
  have h2 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by
    rw [Real.cos_sub]
  have h3 : Real.cos (β - γ) = Real.cos β * Real.cos γ + Real.sin β * Real.sin γ := by
    rw [Real.cos_sub]
  have h4 : Real.cos (γ - α) = Real.cos γ * Real.cos α + Real.sin γ * Real.sin α := by
    rw [Real.cos_sub]

  have h5 : (Real.cos α + Real.cos β + Real.cos γ) ^ 2 = 1 / 5 := by
    calc
      (Real.cos α + Real.cos β + Real.cos γ) ^ 2 = (Real.sqrt (1 / 5)) ^ 2 := by rw [h₀]
      _ = 1 / 5 := by
        rw [Real.sq_sqrt]
        all_goals norm_num

  have h6 : (Real.sin α + Real.sin β + Real.sin γ) ^ 2 = 4 / 5 := by
    calc
      (Real.sin α + Real.sin β + Real.sin γ) ^ 2 = (Real.sqrt (4 / 5)) ^ 2 := by rw [h₁]
      _ = 4 / 5 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
  
  have h7 : (Real.cos α + Real.cos β + Real.cos γ) ^ 2 + (Real.sin α + Real.sin β + Real.sin γ) ^ 2 = 1 := by
    rw [h5, h6]
    norm_num
  
  have h8 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  have h9 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
  have h10 : Real.cos γ ^ 2 + Real.sin γ ^ 2 = 1 := Real.cos_sq_add_sin_sq γ
  have h11 : Real.cos α ^ 2 + Real.cos β ^ 2 + Real.cos γ ^ 2 + Real.sin α ^ 2 + Real.sin β ^ 2 + Real.sin γ ^ 2 = 3 := by
    linarith [h8, h9, h10]

  have h12 : Real.cos α * Real.cos β + Real.cos β * Real.cos γ + Real.cos γ * Real.cos α + Real.sin α * Real.sin β + Real.sin β * Real.sin γ + Real.sin γ * Real.sin α = -1 := by
    nlinarith [h7, h11, Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β, Real.cos_sq_add_sin_sq γ]

  rw [h2, h3, h4]
  linarith [h12]