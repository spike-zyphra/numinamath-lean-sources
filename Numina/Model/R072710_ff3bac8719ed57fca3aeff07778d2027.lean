import Mathlib

theorem algebra_207532 (α β : ℝ) (h₀ : Real.sin α + Real.cos β = 1 / 4) (h₁ : Real.cos α + Real.sin β = -8 / 5) :
    Real.sin (α + β) = 249 / 800 := by
  have h2 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
    rw [Real.sin_add]
  have h3 : (Real.sin α + Real.cos β)^2 = (1 / 4)^2 := by
    rw [h₀]
  have h4 : (Real.cos α + Real.sin β)^2 = (-8 / 5)^2 := by
    rw [h₁]
  have h5 : (Real.sin α + Real.cos β)^2 + (Real.cos α + Real.sin β)^2 = (1 / 4)^2 + (-8 / 5)^2 := by 
    rw [h3, h4]
  have h6 : (Real.sin α + Real.cos β)^2 + (Real.cos α + Real.sin β)^2 =
  (Real.sin α^2 + Real.cos α^2) + (Real.sin β^2 + Real.cos β^2) + 2 * (Real.sin α * Real.cos β + Real.cos α * Real.sin β) := by
    ring
  have h7 : Real.sin α^2 + Real.cos α^2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have h8 : Real.sin β^2 + Real.cos β^2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  have h9 : (Real.sin α + Real.cos β)^2 + (Real.cos α + Real.sin β)^2 = 2 + 2 * (Real.sin α * Real.cos β + Real.cos α * Real.sin β) := by
    linarith [h6, h7, h8]
  have h10 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
    rw [Real.sin_add]
  have h11 : (2 + 2 * (Real.sin α * Real.cos β + Real.cos α * Real.sin β) : ℝ) = (2 + 2 * (Real.sin (α + β) : ℝ) : ℝ) := by 
    rw [show Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β by rw [Real.sin_add]]
    <;> linarith [h10]
  have h12 : (2 + 2 * (Real.sin (α + β) : ℝ) : ℝ) = (1049 / 400 : ℝ) := by 
    have right_side : (1 / 4 : ℝ) ^ 2 + (-8 / 5 : ℝ) ^ 2 = (1049 / 400 : ℝ) := by norm_num
    linarith [h5, h9, right_side]
  have h13 : Real.sin (α + β) = (249 / 800 : ℝ) := by
    linarith [h12]
  exact h13