import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_152225 {x y z : ℝ} (α : ℝ) (h₀ : α = arccos (-1/5)) (h₁ : y - x = α)
    (h₂ : z - y = α) (h₃ : (2 + sin y)^2 = (2 + sin x) * (2 + sin z)) :
    sin y = -1/5 := by
  have h4 : x = y - α := by linarith
  have h5 : z = y + α := by linarith
  have h6 : sin x = sin y * cos α - cos y * sin α := by 
    rw [show x = y - α by linarith]
    rw [sin_sub]
    <;> simp [sin_add, cos_add]
    all_goals ring
  have h7 : sin z = sin y * cos α + cos y * sin α := by 
    rw [show z = y + α by linarith]
    rw [sin_add]
    <;> simp [sin_add, cos_add]
    all_goals ring
  have h8 : cos α = -1/5 := by 
    rw [h₀]
    have h9 : cos (arccos (-1/5)) = -1/5 := by 
      apply cos_arccos 
      all_goals norm_num 
    linarith [h9]
  have h10 : sin α ≥ 0 := by
    have h2 : α ≥ 0 := by 
      rw [h₀]
      apply arccos_nonneg 
      all_goals norm_num 
    have h3 : α ≤ Real.pi := by 
      rw [h₀]
      apply arccos_le_pi 
      all_goals norm_num 
    have h4 : sin α ≥ 0 := by 
      apply sin_nonneg_of_nonneg_of_le_pi 
      linarith [pi_pos] 
      linarith [pi_pos] 
    linarith [pi_pos] 
  have h11 : (sin α) ^ 2 = 24 / 25 := by 
    have h15 : (sin α) ^ 2 + (cos α) ^ 2 = 1 := Real.sin_sq_add_cos_sq α 
    rw [h8] at h15 
    nlinarith 
  have h22 : (cos y) ^ 2 + (sin y) ^ 2 = 1 := Real.cos_sq_add_sin_sq y 
  rw [h6, h7, h8] at h₃
  have h17 : sin y = -1 / 5 := by 
    nlinarith [Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq α, h11, sq_nonneg (sin y + 1 / 5), sq_nonneg (cos y ^ 2 - 1), sq_nonneg (sin y ^ 2 - 1)]
  linarith [h17]
  all_goals nlinarith