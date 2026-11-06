import Mathlib

theorem algebra_151990 (x y z α : ℝ) (h₀ : α = Real.arccos (-2 / 5)) (h₁ : y - x = α)
    (h₂ : z - y = α) (h₃ : (3 + Real.sin y) ^ 2 = (3 + Real.sin x) * (3 + Real.sin z)) :
    Real.sin y = -1 / 10 := by
  have h4 : x = y - α := by linarith
  have h5 : z = y + α := by linarith
  have h6 : Real.sin x = Real.sin y * Real.cos α - Real.cos y * Real.sin α := by
    rw [show x = y - α by linarith]
    rw [Real.sin_sub]
  have h7 : Real.sin z = Real.sin y * Real.cos α + Real.cos y * Real.sin α := by
    rw [show z = y + α by linarith]
    rw [Real.sin_add]
  have h8 : Real.cos α = -2 / 5 := by
    rw [h₀]
    have h9 : Real.cos (Real.arccos (-2 / 5)) = -2 / 5 := by
      apply Real.cos_arccos
      norm_num
      norm_num
    linarith
  have h10 : Real.sin α = Real.sqrt 21 / 5 := by
    rw [h₀]
    have h11 : Real.sin (Real.arccos (-2 / 5)) = Real.sqrt (1 - (-2/5) ^ 2) := by 
      rw [Real.sin_arccos]
    have h12 : Real.sqrt (1 - (-2/5) ^ 2) = Real.sqrt 21 / 5 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h11, h12]
  rw [h6, h7] at h₃
  rw [h8, h10] at h₃
  have h14 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  have h15 : Real.sin y = -1 / 10 := by
    nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num), sq_nonneg (Real.sin y - Real.cos y), sq_nonneg (Real.sin y + Real.cos y), Real.sin_sq_add_cos_sq y]
  linarith