import Mathlib

open Real Set
open scoped Real

theorem algebra_11144 (α β γ : ℝ) (h₀ : α ∈ Ioo 0 Real.pi)
  (h₁ : β ∈ Ioo 0 Real.pi) (h₂ : γ ∈ Ioo 0 Real.pi) (h₃ : α + β + 2 * γ = Real.pi) :
  cos α + cos β + sin (2 * γ) ≤ 3 * sqrt 3 / 2 := by
  rcases h₀ with ⟨hα1, hα2⟩
  rcases h₁ with ⟨hβ1, hβ2⟩
  rcases h₂ with ⟨hγ1, hγ2⟩
  have h4 : α + β = Real.pi - 2 * γ := by
    linarith
  have h5 : cos α + cos β = 2 * sin γ * cos ( (α - β) / 2 ) := by
    have h6 : cos α + cos β = 2 * cos ( (α + β) / 2 ) * cos ( (α - β) / 2 ) := by
      rw [show (α) = ( (α + β) / 2 + (α - β) / 2 ) by ring]
      rw [show (β) = ( (α + β) / 2 - (α - β) / 2 ) by ring]
      rw [cos_add, cos_sub]
      ring
    rw [h6]
    have h7 : (α + β) / 2 = (Real.pi - 2 * γ) / 2 := by
      rw [show (α + β) = Real.pi - 2 * γ by linarith [h₃]]
    rw [h7]
    have h8 : cos ( (Real.pi - 2 * γ) / 2 ) = sin γ := by
      have h9 : (Real.pi - 2 * γ) / 2 = Real.pi / 2 - γ := by ring
      rw [h9]
      rw [cos_pi_div_two_sub]
    rw [h8]
  have h6 : cos ( (α - β) / 2 ) ≤ 1 := by
    apply cos_le_one
  have h7 : cos α + cos β ≤ 2 * sin γ := by
    have h10 : cos ( (α - β) / 2 ) ≤ 1 := h6
    have h9 : 2 * sin γ * cos ( (α - β) / 2 ) ≤ 2 * sin γ := by
      have h10 : cos ( (α - β) / 2 ) ≤ 1 := h6
      have h11 : 2 * sin γ ≥ 0 := by
        have hγ1' : 0 < γ := hγ1
        have hγ2' : γ < Real.pi := hγ2
        have h12 : 0 < sin γ := by
          apply sin_pos_of_pos_of_lt_pi
          linarith
          linarith
        nlinarith
      nlinarith
    linarith [h5, h9]
  have h8 : sin (2 * γ) = 2 * sin γ * cos γ := by
    rw [sin_two_mul]
  have h11 : 2 * sin γ + 2 * sin γ * cos γ ≤ 3 * sqrt 3 / 2 := by
    nlinarith [sq_nonneg (sin γ - Real.sqrt 3 / 2), sq_nonneg (cos γ - 1 / 2), 
        Real.sqrt_pos.mpr (show (0: ℝ) < 3 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (3: ℝ) by norm_num), sin_sq_add_cos_sq γ, 
          sq_nonneg (sin γ), sq_nonneg (cos γ - 1 / 2), 
          sin_pos_of_pos_of_lt_pi hγ1 (show γ < Real.pi by linarith) ]
  linarith [h7, h8, h11]