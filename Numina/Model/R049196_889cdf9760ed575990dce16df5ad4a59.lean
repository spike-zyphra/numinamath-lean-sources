import Mathlib

theorem algebra_124665 (α β : ℝ) (h : 3 * (Real.sin α)^2 + 2 * (Real.sin β)^2 - 2 * (Real.sin α) = 0) :
    14 / 9 ≤ (Real.cos α)^2 + (Real.cos β)^2 ∧ (Real.cos α)^2 + (Real.cos β)^2 ≤ 2 := by
  have h4 : 0 ≤ Real.sin α := by 
    nlinarith [sq_nonneg (Real.sin β), sq_nonneg (Real.sin α - (2 / 3)), sq_nonneg (Real.sin α), sq_nonneg (Real.sin β - 1), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
  have h5 : Real.sin α ≤ 2 / 3 := by 
    nlinarith [sq_nonneg (Real.sin β), sq_nonneg (Real.sin α), sq_nonneg (Real.sin α - (2 / 3)), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
  have eq1 : (Real.cos α)^2 + (Real.cos β)^2 = (1/2) * (Real.sin α)^2 - Real.sin α + 2 := by
    have hcosα : (Real.cos α)^2 = 1 - (Real.sin α)^2 := Real.cos_sq' α
    have hcosβ : (Real.cos β)^2 = 1 - (Real.sin β)^2 := Real.cos_sq' β
    have hsinβ_sq : (Real.sin β)^2 = Real.sin α - (3/2) * (Real.sin α)^2 := by
      nlinarith
    rw [hcosα, hcosβ, hsinβ_sq]
    ring
  rw [eq1]
  constructor
  · -- Prove the lower bound
    nlinarith [sq_nonneg (Real.sin α - 2 / 3), sq_nonneg (Real.sin α - 0)]
  · -- Prove the upper bound
    nlinarith [sq_nonneg (Real.sin α), sq_nonneg (Real.sin α - 0)]