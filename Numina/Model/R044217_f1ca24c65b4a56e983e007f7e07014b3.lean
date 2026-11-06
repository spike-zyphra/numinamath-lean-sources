import Mathlib

theorem algebra_4804 {α β : ℝ} (h : α^2 - 15*α + 9 = 0) (h' : β^2 - 15*β + 9 = 0)
    (h''' : α ≠ β) : 2*α*β^2 + 2*α^2*β - 5*α*β = 225 := by
  have h1 : α - β ≠ 0 := by
    intro h2
    apply h'''
    linarith
  have h2 : α + β = 15 := by 
    have h3 : α^2 - β^2 - 15 * (α - β) = 0 := by 
      nlinarith
    have h4 : (α - β) * (α + β - 15) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- α - β = 0 
      exfalso
      apply h'''
      linarith
    · -- α + β - 15 = 0 
      linarith
  have h3 : α * β = 9 := by 
    nlinarith [sq_pos_of_ne_zero (show (α - β) ≠ 0 by exact h1), sq_nonneg (α - β)]
  have h4 : 2 * α * β^2 + 2 * α^2 * β - 5 * α * β = 225 := by
    have h5 : 2 * α * β^2 + 2 * α^2 * β - 5 * α * β = 2 * (α * β) * (α + β) - 5 * (α * β) := by 
      ring
    rw [h5]
    rw [show α + β = 15 by linarith [h2], show α * β = 9 by linarith [h3]]
    all_goals
      norm_num 
  linarith [h4]