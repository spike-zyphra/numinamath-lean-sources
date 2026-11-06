import Mathlib

theorem algebra_2901 {α β : ℝ} (h : α ≠ β) (h1 : α^2 + 5 * α + 3 = -7 * α + 6) (h2 : β^2 + 5 * β + 3 = -7 * β + 6) :
    1 / α + 1 / β = 4 := by

  have h1' : α^2 + 12 * α - 3 = 0 := by 
    nlinarith
  
  have h2' : β^2 + 12 * β - 3 = 0 := by 
    nlinarith
  
  have h3 : (β - α) * (β + α + 12) = 0 := by
    nlinarith [h1', h2']

  cases' (mul_eq_zero.mp h3) with h4 h5

  · -- Case where β - α = 0 (contradicts α ≠ β)
    exfalso
    have h6 : β = α := by linarith 
    have h7 : α = β := by linarith
    contradiction
  
  · -- Case where β + α + 12 = 0, so α + β = -12
    have h6 : α + β = -12 := by 
      linarith

    have h7 : α * β = -3 := by
      have eq1 : α^2 + β^2 = 150 := by
        have eq2 : α^2 + β^2 + 12 * (α + β) - 6 = 0 := by 
          nlinarith [h1', h2']
        rw [h6] at eq2
        nlinarith

      have eq3 : (α + β)^2 = α^2 + β^2 + 2 * (α * β) := by 
        ring

      rw [h6, eq1] at eq3
      nlinarith

    have h8 : α ≠ 0 := by 
      intro h9
      rw [h9] at h1'
      nlinarith

    have h9 : β ≠ 0 := by 
      intro h10
      rw [h10] at h2'
      nlinarith

    field_simp [h8, h9]
    nlinarith [h6, h7]