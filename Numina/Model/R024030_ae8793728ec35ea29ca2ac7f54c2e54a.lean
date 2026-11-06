import Mathlib

theorem algebra_214005 (α β : ℝ) (h : Real.sin α * Real.sin β = 1) : Real.cos (α + β) = -1 := by
  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h2 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have h3 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by linarith
  have h4 : Real.sin β ^ 2 = 1 - Real.cos β ^ 2 := by linarith
  have h5 : Real.sin α ^ 2 * Real.sin β ^ 2 = 1 := by
    calc
      Real.sin α ^ 2 * Real.sin β ^ 2 = (Real.sin α * Real.sin β) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [h]
      _ = 1 := by norm_num
  have h6 : (Real.cos α ^ 2) * (Real.cos β ^ 2) = Real.cos α ^ 2 + Real.cos β ^ 2 := by
    nlinarith [h1, h2, h3, h4, h5]
  have h7 : Real.cos α * Real.cos β = 0 := by
    nlinarith [sq_nonneg (Real.cos α - Real.cos β), sq_nonneg (Real.cos α + Real.cos β), sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.sin α + Real.sin β), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, sq_nonneg (Real.sin α), sq_nonneg (Real.sin β), sq_nonneg (Real.cos α), sq_nonneg (Real.cos β)]
  have h8 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := by
    rw [Real.cos_add]
  rw [h8, h]
  linarith [h7]