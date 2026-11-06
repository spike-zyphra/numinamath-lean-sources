import Mathlib

theorem algebra_190768 (α β : ℝ) (h₁ : Real.sin α + Real.sqrt 3 * Real.sin β = 1)
    (h₂ : Real.cos α + Real.sqrt 3 * Real.cos β = Real.sqrt 3) :
    Real.cos (α - β) = 0 := by
  have h3 : (Real.sin α + Real.sqrt 3 * Real.sin β)^2 + (Real.cos α + Real.sqrt 3 * Real.cos β)^2 = (1 : ℝ) + (Real.sqrt 3) ^ 2 := by
    rw [h₁, h₂]
    all_goals ring_nf
    <;> norm_num [Real.sq_sqrt]
    <;> ring_nf
  have h4 : (Real.sin α + Real.sqrt 3 * Real.sin β)^2 + (Real.cos α + Real.sqrt 3 * Real.cos β)^2 = 4 := by
    have h5 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    nlinarith [h3, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sqrt_nonneg 3]
  have h6 : (Real.sin α + Real.sqrt 3 * Real.sin β)^2 + (Real.cos α + Real.sqrt 3 * Real.cos β)^2 =
      (Real.sin α) ^ 2 + (Real.cos α)^ 2 + 3 * ((Real.sin β)^ 2 + (Real.cos β)^ 2) + 2 * Real.sqrt 3 * (Real.sin α * Real.sin β + Real.cos α * Real.cos β) := by
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
  have h7 : (Real.sin α: ℝ) ^ 2 + (Real.cos α)^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h8 : (Real.sin β)^ 2 + (Real.cos β)^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have h9 : Real.sin α * Real.sin β + Real.cos α * Real.cos β = 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), h7, h8, h4, h6, Real.sqrt_nonneg 3]
  have h10 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by
    rw [Real.cos_sub]
  rw [h10]
  nlinarith [h9]