import Mathlib

theorem algebra_313646 (α β : ℝ) (a b : ℝ) (h₀ : Real.cos α + Real.cos β = a)
    (h₁ : Real.sin α + Real.sin β = b) (h₂ : a^2 + b^2 ≠ 0) :
    Real.cos (α + β) = (a^2 - b^2) / (a^2 + b^2) := by
  have h5 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := by
    rw [Real.cos_add]
  
  have h7 : a^2 + b^2 = 2 + 2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by
    calc
      a^2 + b^2 = (Real.cos α + Real.cos β) ^ 2 + (Real.sin α + Real.sin β) ^ 2 := by
        rw [h₀, h₁]
      _ = (Real.cos α ^ 2 + Real.sin α ^ 2) + (Real.cos β ^ 2 + Real.sin β ^ 2) + 2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by
        ring
      _ = 1 + 1 + 2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by
        have h9 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
        have h10 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
        rw [h9, h10]
      _ = 2 + 2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by
        ring
  
  have h9 : a^2 - b^2 = (Real.cos α ^ 2 - Real.sin α ^ 2) + (Real.cos β ^ 2 - Real.sin β ^ 2) + 2 * (Real.cos α * Real.cos β - Real.sin α * Real.sin β) := by
    have h8 : a^2 - b^2 = (Real.cos α + Real.cos β)^2 - (Real.sin α + Real.sin β)^2 := by
      rw [h₀, h₁]
    rw [h8]
    have h11 : (Real.cos α + Real.cos β) ^ 2 - (Real.sin α + Real.sin β) ^ 2 = (Real.cos α ^ 2 - Real.sin α ^ 2) + (Real.cos β ^ 2 - Real.sin β ^ 2) + 2 * (Real.cos α * Real.cos β - Real.sin α * Real.sin β) := by 
      nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
    linarith [h11]
  
  have h10 : (Real.cos α * Real.cos β - Real.sin α * Real.sin β) * (a^2 + b^2) = a^2 - b^2 := by
    rw [show a^2 + b^2 = 2 + 2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) by linarith [h7]]
    rw [show a^2 - b^2 = (Real.cos α ^ 2 - Real.sin α ^ 2) + (Real.cos β ^ 2 - Real.sin β ^ 2) + 2 * (Real.cos α * Real.cos β - Real.sin α * Real.sin β) by linarith [h9]]
    have h11 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
    have h12 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
    nlinarith [Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β]

  rw [h5]
  field_simp [h₂]
  <;> linarith [h10]