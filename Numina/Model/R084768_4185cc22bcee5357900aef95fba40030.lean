import Mathlib

open Real Set
open scoped Real

theorem algebra_164064 (α β γ : ℝ) (h₀ : α ∈ Ioo 0 Real.pi)
  (h₁ : β ∈ Ioo 0 Real.pi) (h₂ : γ ∈ Ioo 0 Real.pi)
  (h₃ : α + β + 2 * γ = Real.pi) :
  cos α + cos β + sin (2 * γ) ≤ 3 * sqrt 3 / 2 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h4 : sin (2 * γ) = 2 * sin γ * cos γ := by
    rw [sin_two_mul]
  have h5 : cos α + cos β = 2 * sin γ * cos ( (α - β) / 2 ) := by
    have h6 : cos α + cos β = 2 * cos ( (α + β) / 2 ) * cos ( (α - β) / 2 ) := by
      rw [cos_add_cos]
      all_goals ring
    rw [h6]
    have h8 : (α + β) / 2 = Real.pi / 2 - γ := by
      linarith [h₃]
    have h9 : cos ( (α + β) / 2 ) = sin γ := by
      rw [h8]
      rw [cos_pi_div_two_sub]
    rw [h9]
    <;> ring
  have h7 : cos α + cos β + sin (2 * γ) = 2 * sin γ * ( cos ( (α - β) / 2 ) + cos γ ) := by
    rw [h5, h4]
    <;> ring
  rw [h7]
  have h8 : cos ( (α - β) / 2 ) ≤ 1 := by
    apply cos_le_one
  have h9 : cos γ ≤ 1 := by
    apply cos_le_one
  have h10 : sin γ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h11 : 2 * sin γ * (1 + cos γ ) ≤ 3 * sqrt 3 / 2 := by 
    nlinarith [sq_nonneg (sin γ - Real.sqrt 3 / 2), sq_nonneg (cos γ - 1 / 2), 
      Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
      Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), 
      Real.cos_pi_div_three, Real.sin_pi_div_three, 
      Real.pi_pos, 
      Real.sin_sq_add_cos_sq γ, 
      Real.cos_sq_add_sin_sq γ
    ]
  have h13 : 2 * sin γ * (cos ( (α - β) / 2 ) + cos γ ) ≤ 2 * sin γ * (1 + cos γ ) := by
    nlinarith [h8, h9]
  linarith [h13, h11]