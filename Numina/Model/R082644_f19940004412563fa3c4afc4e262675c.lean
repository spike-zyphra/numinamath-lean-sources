import Mathlib

theorem algebra_118651 (α β k : ℝ) (h₁ : α ≠ β) (h₂ : α^2 - 2 * k * α + k + 20 = 0)
    (h₃ : β^2 - 2 * k * β + k + 20 = 0) :
    (α + 1)^2 + (β + 1)^2 ≥ 18 ∧
    ((α + 1)^2 + (β + 1)^2 = 18 ↔ k = -1) := by
  -- Compute α + β = 2k by subtracting the two equations
  have h4 : α + β = 2 * k := by
    have h5 : α^2 - β^2 = 2 * k * (α - β) := by
      nlinarith
    have h6 : α^2 - β^2 = (α - β) * (α + β) := by
      ring
    rw [h6] at h5
    have h7 : α - β ≠ 0 := by
      intro h
      apply h₁
      linarith
    have h8 : α + β = 2 * k := by
      apply (mul_left_inj' h7).mp
      linarith
    linarith
  -- Compute α² + β² by summing the two equations
  have h5 : α^2 + β^2 = 4 * k^2 - 2 * k - 40 := by 
    nlinarith [h₂, h₃, h4]
  -- Express (α + 1)² + (β + 1)² in terms of k
  have h6 : (α + 1)^2 + (β + 1)^2 = 4 * k^2 + 2 * k - 38 := by
    nlinarith [h5, h4]
  constructor
  · -- Prove that (α + 1)² + (β + 1)² ≥ 18
    nlinarith [sq_nonneg (α - β), sq_nonneg (k + 1), sq_pos_of_ne_zero (show α - β ≠ 0 by intro h; apply h₁; linarith), sq_nonneg (α + β - 2 * k), sq_nonneg (k - 5), sq_nonneg (k + 4)]
  · -- Prove that (α + 1)² + (β + 1)² = 18 ↔ k = -1
    constructor
    · -- Forward implication
      intro heq
      have h8 : (α + 1)^2 + (β + 1)^2 = 18 := by linarith
      have h9 : (k + 1) ^ 2 = 0 := by 
        nlinarith [h8, sq_nonneg (α - β), sq_nonneg (k + 1), sq_pos_of_ne_zero (show α - β ≠ 0 by intro h; apply h₁; linarith), sq_nonneg (α + β - 2 * k), sq_nonneg (k - 5), sq_nonneg (k + 4)]
      have hk : k + 1 = 0 := by 
        rwa [sq_eq_zero_iff] at h9
      linarith
    · -- Backward implication
      intro hk
      rw [h6]
      nlinarith [sq_nonneg (k + 1), sq_nonneg (α - β), sq_pos_of_ne_zero (show α - β ≠ 0 by intro h; apply h₁; linarith), sq_nonneg (α + β - 2 * k), sq_nonneg (k - 5), sq_nonneg (k + 4)]