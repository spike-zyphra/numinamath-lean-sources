import Mathlib

theorem algebra_13423 {α β : ℝ} (h₁ : α^2 - 7 * α - 9 = 0) (h₂ : β^2 - 7 * β - 9 = 0)
    (h₃ : α ≠ β) : 3 * α^2 * β + 3 * α * β^2 = -189 := by
  have h4 : α^2 - β^2 - 7 * (α - β) = 0 := by
    nlinarith 
  have h5 : (α - β) * (α + β - 7) = 0 := by
    nlinarith [h4]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- α - β = 0, which would imply α = β, contradicting α ≠ β
    exfalso
    exact h₃ (by linarith)
  · -- α + β - 7 = 0, so α + β = 7
    have h7' : α + β = 7 := by linarith
    have h8 : α * β = -9 := by 
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h₃)]
    nlinarith [h7', h8]