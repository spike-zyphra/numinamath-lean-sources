import Mathlib

open Real Set
open scoped Real

theorem inequalities_154967 (α β γ : Real) (h : α ∈ Ioo 0 (π / 2)) (h' : β ∈ Ioo 0 (π / 2))
    (h'' : γ ∈ Ioo 0 (π / 2)) (h''' : α + β + γ = π) :
    sin α + sin β + sin γ > 2 := by
  rcases h with ⟨h1, h2⟩
  rcases h' with ⟨h3, h4⟩
  rcases h'' with ⟨h5, h6⟩
  have h7 : α + β > π / 2 := by 
    nlinarith 
  have h8 : α + β < π := by 
    nlinarith 
  have h9 : γ = π - (α + β) := by 
    nlinarith 
  have h10 : sin γ = sin (α + β) := by 
    have h9' : γ = π - (α + β) := h9 
    rw [h9']
    have h11 : sin (π - (α + β)) = sin (α + β) := by 
      rw [sin_pi_sub]
    linarith [h11]
  have h11 : sin (α + β) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi 
      · -- Show that 0 < α + β 
        linarith 
      · -- Show that α + β < π 
        linarith
  have h10' : sin α + sin β + sin γ > 2 := by 
    rw [show sin γ = sin (α + β) by linarith [h10] ] 
    have eq1' : sin (α + β) = sin α * cos β + cos α * sin β := by 
      rw [sin_add]
    rw [eq1']
    have h11' : sin α > 0 := by apply sin_pos_of_pos_of_lt_pi; linarith; linarith [Real.pi_gt_three, h2]
    have h12' : sin β > 0 := by apply sin_pos_of_pos_of_lt_pi; linarith; linarith [Real.pi_gt_three, h4]
    have h13' : cos α > 0 := by apply cos_pos_of_mem_Ioo; constructor <;> linarith
    have h14' : cos β > 0 := by apply cos_pos_of_mem_Ioo; constructor <;> linarith 
    have h15 : cos (α + β) < 0 := by 
      have h15' : α + β > π / 2 := h7
      have h17 : α + β < π := h8 
      apply cos_neg_of_pi_div_two_lt_of_lt 
      all_goals 
        linarith 
    have h16 : cos α * cos β < sin α * sin β := by
      have h17 : cos (α + β) = cos α * cos β - sin α * sin β := by 
        rw [cos_add]
      nlinarith [h17, h15]
    nlinarith [sq_pos_of_pos h11', sq_pos_of_pos h12', sq_pos_of_pos h13', sq_pos_of_pos h14', 
          sin_sq_add_cos_sq α, sin_sq_add_cos_sq β, 
          mul_pos h11' h12', mul_pos h11' h13', mul_pos h11' h14', 
          mul_pos h12' h13', mul_pos h12' h14', mul_pos h13' h14', 
          h16, mul_pos h11' h14', mul_pos h12' h13']
  linarith [h10']