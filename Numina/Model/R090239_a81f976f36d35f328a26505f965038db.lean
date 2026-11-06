import Mathlib

theorem algebra_2861
  (α β : ℝ)
  (hroots : α ≠ β ∧ α^2 + 20 * α + 22 = 0 ∧ β^2 + 20 * β + 22 = 0) :
  α^3 + β^3 = -6680 := by 
  have h1 : α^2 + 20 * α + 22 = 0 := hroots.right.left
  have h2 : β^2 + 20 * β + 22 = 0 := hroots.right.right
  have hne : α ≠ β := hroots.left

  have h3 : α^2 - β^2 + 20 * (α - β) = 0 := by 
    nlinarith
  
  have h4 : (α - β) * (α + β + 20) = 0 := by 
    linarith [h3]
  
  have h5 : α + β = -20 := by 
    cases' (mul_eq_zero.mp h4) with h6 h7
    · -- Case $\alpha - \beta = 0$, which contradicts $\alpha \neq \beta$
      exfalso
      exact hne (by linarith)
    · -- Case $\alpha + \beta + 20 = 0$
      linarith

  have h8 : α * β = 22 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hne), h5]

  have h9 : α^3 + β^3 = (α + β) ^ 3 - 3 * (α * β) * (α + β) := by 
    ring

  rw [h9]
  rw [h5, h8]
  norm_num