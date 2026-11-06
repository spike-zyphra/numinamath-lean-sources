import Mathlib

theorem algebra_152109 (x y z α : ℝ) 
    (h₀ : α = Real.arccos (1 / 9))
    (h₁ : y - x = α)
    (h₂ : z - y = α) 
    (h₃ : (5 + Real.cos y) ^ 2 = (5 + Real.cos x) * (5 + Real.cos z) ∧ 5 + Real.cos x ≠ 5 + Real.cos y ∧ 5 + Real.cos y ≠ 5 + Real.cos z ∧ 5 + Real.cos x ≠ 5 + Real.cos z):
    Real.cos y = -1 / 9 := by
  rcases h₃ with ⟨h₄, h₅, h₆, h₇⟩
  have h8 : x = y - α := by linarith
  have h9 : z = y + α := by linarith

  have h10 : Real.cos x = Real.cos y * Real.cos α + Real.sin y * Real.sin α := by
    rw [show x = y - α by linarith]
    rw [Real.cos_sub]
  have h11 : Real.cos z = Real.cos y * Real.cos α - Real.sin y * Real.sin α := by
    rw [show z = y + α by linarith]
    rw [Real.cos_add]
  have h12 : Real.cos α = 1 / 9 := by
    rw [h₀]
    have h12 : Real.cos (Real.arccos (1 / 9)) = 1 / 9 := by
      apply Real.cos_arccos
      all_goals norm_num
    linarith
  have h13 : Real.sin α ^ 2 = 80 / 81 := by
    have h14 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    rw [h12] at h14
    nlinarith
  have h15 : Real.sin α ≥ 0 := by
    have hα : 0 ≤ α := by
      rw [h₀]
      apply Real.arccos_nonneg
    have hα2 : α ≤ Real.pi := by
      rw [h₀]
      apply Real.arccos_le_pi
    have h16 : 0 ≤ Real.sin α := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      all_goals linarith [hα, hα2]
    linarith
  have h14 : Real.sin α = 4 * Real.sqrt 5 / 9 := by
    have h17 : Real.sin α ^ 2 = 80 / 81 := h13
    have h18 : Real.sin α ≥ 0 := h15
    have hsinα_eq : Real.sin α = Real.sqrt (80 / 81) := by
      have h20 : Real.sin α ≥ 0 := h18
      have h21 : Real.sin α = Real.sqrt (Real.sin α ^ 2) := by
        rw [Real.sqrt_sq (show 0 ≤ Real.sin α by linarith)]
      rw [h21, h17]
    have hsqrt_eq : Real.sqrt (80 / 81 : ℝ) = 4 * Real.sqrt 5 / 9 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [hsqrt_eq] at hsinα_eq
    linarith
  rw [h10, h11, h12, h14] at h₄
  have h15 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), sq_nonneg (Real.sin y), sq_nonneg (Real.sqrt (5 : ℝ)), sq_nonneg (Real.sin y - 0), sq_nonneg (Real.cos y + 1/9)]