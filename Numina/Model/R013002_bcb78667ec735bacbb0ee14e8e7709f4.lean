import Mathlib

open Real Set
open scoped Real

theorem algebra_326775 (α β : ℝ) (h₁ : α ∈ Ioo 0 (π / 2)) (h₂ : β ∈ Ioo 0 (π / 2))
    (h₃ : 3 * sin α ^ 2 + 2 * sin β ^ 2 = 1) (h₄ : 3 * sin (2 * α) - 2 * sin (2 * β) = 0) :
    sin (α + 2 * β) = 1 := by
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h5 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₁₁, h₁₂, Real.pi_pos]
    linarith [h₁₁, h₁₂, Real.pi_pos]
  have h6 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h₁₁, h₁₂, Real.pi_pos]
    linarith [h₁₁, h₁₂, Real.pi_pos]
  have h7 : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₂₁, h₂₂, Real.pi_pos]
    linarith [h₂₁, h₂₂, Real.pi_pos]
  have h8 : cos β > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h₂₁, h₂₂, Real.pi_pos]
    linarith [h₂₁, h₂₂, Real.pi_pos]
  have eq1 : sin (2 * α) = 2 * sin α * cos α := by
    rw [sin_two_mul]
  have eq2 : sin (2 * β) = 2 * sin β * cos β := by
    rw [sin_two_mul]
  rw [eq1] at h₄
  rw [eq2] at h₄
  have eq4 : 3 * sin α * cos α = 2 * sin β * cos β := by linarith
  have eq5 : sin (α + 2 * β) = sin α * cos (2 * β) + cos α * sin (2 * β) := by
    rw [sin_add]
  have eq6 : cos (2 * β) = 2 * cos β ^ 2 - 1 := by
    rw [cos_two_mul]
  have eq7 : sin (2 * β) = 2 * sin β * cos β := by
    rw [sin_two_mul]
  rw [eq5]
  rw [eq6, eq7]
  have h9 : cos α ^ 2 = 1 - sin α ^ 2 := by
    have h10 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    linarith
  have h10 : cos β ^ 2 = 1 - sin β ^ 2 := by
    have h11 : sin β ^ 2 + cos β ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq β
    linarith
  nlinarith [mul_pos h5 h6, mul_pos h5 h7, 
          mul_pos h5 h8, mul_pos h6 h7, 
          mul_pos h6 h8, mul_pos h7 h8 
        ]