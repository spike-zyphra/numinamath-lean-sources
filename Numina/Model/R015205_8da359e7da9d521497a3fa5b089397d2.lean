import Mathlib

open Real Set
open scoped Real

theorem inequalities_224619 (α β : ℝ) (h₁ : α ∈ Ioo 0 (π/2)) (h₂ : β ∈ Ioo 0 (π/2)) :
    sin α ^ 3 / sin β + cos α ^ 3 / cos β ≥ 1 := by
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h3 : sin β > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₂₁, h₂₂, Real.pi_pos]
    linarith [h₂₁, h₂₂, Real.pi_pos]
  have h4 : cos β > 0 := by 
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h₂₁, h₂₂, Real.pi_pos]
    linarith [h₂₁, h₂₂, Real.pi_pos]
  have h5 : sin α > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₁₁, h₁₂, Real.pi_pos]
    linarith [h₁₁, h₁₂, Real.pi_pos]
  have h6 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h₁₁, h₁₂, Real.pi_pos]
    linarith [h₁₁, h₁₂, Real.pi_pos]
  have h7 : sin α ^ 3 / sin β + cos α ^ 3 / cos β - (1 : ℝ) ≥ 0 := by
    have h8 : sin β * cos β > 0 := by 
      nlinarith [h3, h4, Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith) (show β < Real.pi by linarith)]
    have h9 : sin α ^ 3 / sin β + cos α ^ 3 / cos β - (1 : ℝ) = (cos β * (sin α ^ 3) + sin β * (cos α ^ 3) - sin β * cos β) / (sin β * cos β) := by 
      field_simp [h3, h4]
      <;> ring
    rw [h9] at *
    have h10 : cos β * (sin α ^ 3) + sin β * (cos α ^ 3) - sin β * cos β ≥ 0 := by 
      nlinarith [sq_nonneg (sin α - sin β), sq_nonneg (cos α - cos β), 
          sq_nonneg (sin α * cos β - cos α * sin β), 
          sq_nonneg (sin α ^ 2 - cos α ^ 2), 
          sq_nonneg (sin β ^ 2 - cos β ^ 2), 
          sq_nonneg (sin α - cos α), 
          sq_nonneg (sin β - cos β), 
          sq_nonneg (sin α * cos α - sin β * cos β), 
          Real.sin_sq_add_cos_sq α, 
          Real.sin_sq_add_cos_sq β, 
          mul_pos h5 h6, 
          mul_pos h5 h3, 
          mul_pos h5 h4, 
          mul_pos h6 h3, 
          mul_pos h6 h4, 
          mul_pos h3 h4, 
          mul_pos (show 0 < Real.sin α by linarith) (show 0 < Real.sin β by linarith), 
          mul_pos (show 0 < Real.sin α by linarith) (show 0 < Real.cos β by linarith), 
          mul_pos (show 0 < Real.cos α by linarith) (show 0 < Real.sin β by linarith), 
          mul_pos (show 0 < Real.cos α by linarith) (show 0 < Real.cos β by linarith)
        ]
    apply div_nonneg 
    linarith
    linarith 
  linarith