import Mathlib

open Real Set
open scoped Real

theorem algebra_147739 (α β : Real) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : sin α ^ 2 + sin β ^ 2 = sin (α + β)) :
    α + β = π / 2 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  have h₃ : sin (α + β) = sin α * cos β + cos α * sin β := by 
    rw [sin_add]
  rw [h₃] at h₂
  by_cases h : α + β < π / 2
  · -- Assume that $\alpha + \beta < \pi/2$
    have h₄ : α < π / 2 - β := by linarith
    have h₅ : sin α < cos β := by
      have h₆ : α < π / 2 - β := h₄
      have h₇ : sin α < sin (π / 2 - β) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          linarith [h₀₁, h₀₂, h₁₁, h₁₂]
      have h₈ : sin (π / 2 - β) = cos β := by 
        rw [sin_pi_div_two_sub]
      linarith [h₈]
    have h₆ : cos α > sin β := by 
      have h₇ : α < π / 2 - β := h₄
      have h₈ : cos α = sin (π / 2 - α) := by 
        rw [← sin_pi_div_two_sub]
      have h₉ : π / 2 - α > β := by 
        nlinarith [h₇, Real.pi_pos]
      have h₆ : sin (π / 2 - α) > sin β := by 
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          linarith [h₀₁, h₀₂, h₁₁, h₁₂, Real.pi_pos]
      rw [h₈]
      linarith
    nlinarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith) (show α < Real.pi by linarith [Real.pi_gt_three, h₀₂]), Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith) (show β < Real.pi by linarith [Real.pi_gt_three, h₁₂]), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, mul_pos (show 0 < sin α by apply sin_pos_of_pos_of_lt_pi; linarith; linarith) (show 0 < sin β by apply sin_pos_of_pos_of_lt_pi; linarith; linarith), sq_nonneg (sin α - cos β), sq_nonneg (cos α - sin β), Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β]
  by_cases h' : α + β > π / 2
  · -- Assume that $\alpha + \beta > \pi/2$
    have h₄ : α > π / 2 - β := by linarith
    have h₅ : sin α > cos β := by
      have h₆ : α > π / 2 - β := h₄
      have h₇ : sin α > sin (π / 2 - β) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          linarith [h₀₁, h₀₂, h₁₁, h₁₂]
      have h₈ : sin (π / 2 - β) = cos β := by 
        rw [sin_pi_div_two_sub]
      linarith [h₈]
    have h₆ : cos α < sin β := by 
      have h₇ : α > π / 2 - β := h₄
      have h₈ : cos α = sin (π / 2 - α) := by 
        rw [← sin_pi_div_two_sub]
      have h₉ : π / 2 - α < β := by 
        nlinarith [h₇, Real.pi_pos]
      have h₆ : sin (π / 2 - α) < sin β := by 
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
          linarith [h₀₁, h₀₂, h₁₁, h₁₂, Real.pi_pos]
      rw [h₈]
      linarith
    nlinarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith) (show α < Real.pi by linarith [Real.pi_gt_three, h₀₂]), Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith) (show β < Real.pi by linarith [Real.pi_gt_three, h₁₂]), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, mul_pos (show 0 < sin α by apply sin_pos_of_pos_of_lt_pi; linarith; linarith) (show 0 < sin β by apply sin_pos_of_pos_of_lt_pi; linarith; linarith), sq_nonneg (sin α - cos β), sq_nonneg (cos α - sin β), Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β]
  linarith