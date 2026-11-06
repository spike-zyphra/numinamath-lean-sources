import Mathlib

theorem algebra_163520 (α β : ℝ) :
    1 - Real.sin α ^ 2 - Real.sin β ^ 2 + 2 * Real.sin α * Real.sin β * Real.cos (α - β) =
    Real.cos (α - β) ^ 2 := by
  have h1 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by
    rw [Real.cos_sub]
  rw [h1]
  have h2 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have h3 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  nlinarith [sq_nonneg (Real.cos α * Real.cos β - Real.sin α * Real.sin β), sq_nonneg (Real.sin α * Real.cos β - Real.sin β * Real.cos α), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, mul_self_nonneg (Real.sin α * Real.sin β - Real.cos α * Real.cos β), mul_self_nonneg (Real.sin α * Real.sin β - Real.sin α * Real.sin β)]
  <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
  <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, sq_nonneg (Real.sin α ^ 2 - Real.sin β ^ 2)]
  <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, sq_nonneg (Real.cos α ^ 2 - Real.cos β ^ 2)]
  <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, sq_nonneg (Real.sin α * Real.sin β - Real.sin α * Real.sin β)]
  <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]