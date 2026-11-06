import Mathlib

theorem algebra_291530 (a b c α β γ : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a * Real.sin α + b * Real.sin β + c * Real.sin γ = 0) (h2 : a * Real.cos α + b * Real.cos β + c * Real.cos γ = 0) :
    Real.sin (β - γ) / a = Real.sin (γ - α) / b ∧ Real.sin (γ - α) / b = Real.sin (α - β) / c := by

  have h3 : Real.sin (β - γ) = Real.sin β * Real.cos γ - Real.cos β * Real.sin γ := by 
    rw [Real.sin_sub]

  have h4 : Real.sin (γ - α) = Real.sin γ * Real.cos α - Real.cos γ * Real.sin α := by 
    rw [Real.sin_sub]

  have h5 : Real.sin (α - β) = Real.sin α * Real.cos β - Real.cos α * Real.sin β := by 
    rw [Real.sin_sub]

  have eq1 : Real.sin (β - γ) / a = Real.sin (γ - α) / b := by
    rw [h3, h4]
    field_simp [ha, hb]
    have eq1' : a * (Real.sin α * Real.cos γ - Real.cos α * Real.sin γ) + b * (Real.sin β * Real.cos γ - Real.cos β * Real.sin γ) = 0 := by
      have h6 : a * Real.sin α + b * Real.sin β + c * Real.sin γ = 0 := h1
      have h7 : a * Real.cos α + b * Real.cos β + c * Real.cos γ = 0 := h2
      -- Multiply first eq by cos γ, second by sin γ, and subtract
      have h8 : (a * Real.sin α + b * Real.sin β + c * Real.sin γ) * Real.cos γ = 0 := by 
        rw [h6]
        norm_num
      have h9 : (a * Real.cos α + b * Real.cos β + c * Real.cos γ) * Real.sin γ = 0 := by 
        rw [h7]
        norm_num
      have h10 : (a * Real.sin α + b * Real.sin β + c * Real.sin γ) * Real.cos γ - (a * Real.cos α + b * Real.cos β + c * Real.cos γ) * Real.sin γ = 0 := by 
        linarith
      linarith
    linarith [eq1']

  have eq2 : Real.sin (γ - α) / b = Real.sin (α - β) / c := by
    rw [h4, h5]
    field_simp [hb, hc] at *
    have eq34 : a * (Real.sin α * Real.cos β - Real.cos α * Real.sin β) + c * (Real.sin γ * Real.cos β - Real.cos γ * Real.sin β) = 0 := by
      have eq31 : (a * Real.sin α + b * Real.sin β + c * Real.sin γ) * Real.cos β = 0 := by 
        rw [h1]
        norm_num 
      have eq32 : (a * Real.cos α + b * Real.cos β + c * Real.cos γ) * Real.sin β = 0 := by 
        rw [h2]
        norm_num 
      have eq33 : (a * Real.sin α + b * Real.sin β + c * Real.sin γ) * Real.cos β - (a * Real.cos α + b * Real.cos β + c * Real.cos γ) * Real.sin β = 0 := by 
        linarith 
      linarith 
    -- Prove the cross-multiplied equation
    have eq13 : (Real.sin γ * Real.cos α - Real.cos γ * Real.sin α) * c = (Real.sin α * Real.cos β - Real.cos α * Real.sin β) * b := by 
      have eq11 : a * (Real.sin α * Real.cos α) + b * (Real.sin β * Real.cos α) + c * (Real.sin γ * Real.cos α) = 0 := by 
        have eq6 : a * Real.sin α * Real.cos α + b * Real.sin β * Real.cos α + c * Real.sin γ * Real.cos α = 0 := by 
          have h6 : a * Real.sin α + b * Real.sin β + c * Real.sin γ = 0 := by linarith [h1]
          have eq51 : (a * Real.sin α + b * Real.sin β + c * Real.sin γ) * Real.cos α = 0 := by 
            rw [h6]
            norm_num 
          linarith 
        linarith [eq6]
      have eq12 : a * (Real.cos α * Real.sin α) + b * (Real.cos β * Real.sin α) + c * (Real.cos γ * Real.sin α) = 0 := by 
        have eq6 : a * Real.cos α * Real.sin α + b * Real.cos β * Real.sin α + c * Real.cos γ * Real.sin α = 0 := by 
          have h7 : a * Real.cos α + b * Real.cos β + c * Real.cos γ = 0 := by linarith [h2]
          have eq61 : (a * Real.cos α + b * Real.cos β + c * Real.cos γ) * Real.sin α = 0 := by 
            rw [h7]
            norm_num 
          linarith 
        linarith [eq6]
      nlinarith [sq_nonneg (Real.sin α), sq_nonneg (Real.sin β), sq_nonneg (Real.sin γ), 
            sq_nonneg (Real.cos α - Real.cos β), sq_nonneg (Real.cos β - Real.cos γ), sq_nonneg (Real.cos γ - Real.cos α), 
            sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.sin β - Real.sin γ), sq_nonneg (Real.sin γ - Real.sin α), 
            Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq γ
           ]
    linarith [eq13]

  exact ⟨eq1, eq2⟩