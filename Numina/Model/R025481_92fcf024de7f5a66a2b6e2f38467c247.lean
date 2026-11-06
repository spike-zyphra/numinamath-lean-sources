import Mathlib

theorem algebra_320994 {α β : ℝ} (hα : α^2 + 3 * α - 1 = 0) (hβ : β^2 - 3 * β - 1 = 0) (hαβ : α * β ≠ 1) :
    α^(-2 : ℤ) + 3 * β = 10 := by 
  have h1 : β ^ 2 - 3 * β = 1 := by 
    nlinarith
  have h2 : α ^ 2 + 3 * α = 1 := by 
    nlinarith
  have h3 : (β + α) * (β - α - 3) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp h3) with h4 h5 
  · -- β + α = 0, so β = -α.
    have h7 : β = -α := by linarith
    have h8 : α ≠ 0 := by 
      by_contra h
      rw [h] at hα
      nlinarith
    have h505 : α ^ (-2 : ℤ) = ((α ^ 2 ) )⁻¹ := by 
      simp [zpow_neg, zpow_ofNat]
    have eq23 : α ^ (-2 : ℤ) = (α + 3) ^ 2 := by
      rw [h505]
      have h14 : α ^ 2 = 1 - 3 * α := by 
        linarith
      have h17 : ((α ^ 2) )⁻¹ = (α + 3) ^ 2 := by
        have h17' : α ≠ 0 := h8
        have eq12 : α ^ 2 ≠ 0 := by
          intro h6
          apply h17'
          nlinarith
        field_simp [eq12]
        nlinarith [sq_pos_of_ne_zero (show α ≠ 0 by exact h8), h14, sq_nonneg (α + 1)]
      exact h17
    have h100 : α ^ (-2 : ℤ) + 3 * β = 10 := by
      rw [eq23]
      rw [h7]
      nlinarith [hα, sq_pos_of_ne_zero (show α ≠ 0 by exact h8), sq_nonneg (α ^ 2 +3 * α -1), sq_nonneg (β ^ 2 -3 * β -1) ]
    linarith [h100]
  · -- This is the case β - α - 3 = 0 
    have h7 : β = α + 3 := by linarith 
    have h512 : α * (α + 3) = 1 := by
      have h140 : α ^ 2 + 3 * α = 1 := by linarith
      calc 
        α * (α + 3) = α ^ 2 + 3 * α := by ring 
        _ = 1 := by linarith [h140]
    have h870 : α * β = α * (α + 3) := by 
      rw [show β = α + 3 by linarith [h7]]
    have h1132 : α * β = 1 := by
      rw [h870]
      linarith [h512]
    contradiction