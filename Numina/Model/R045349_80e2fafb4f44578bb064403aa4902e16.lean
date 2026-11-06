import Mathlib

open Real
open scoped Real

theorem inequalities_206702 (α β γ : ℝ) (h : α ∈ Set.Ioo 0 π)
  (h' : β ∈ Set.Ioo 0 π) (h'' : γ ∈ Set.Ioo 0 π) (h''' : α + β + γ = π) :
  cos α + cos β + cos γ < 2 := by

  rcases h with ⟨hα1, hα2⟩
  rcases h' with ⟨hβ1, hβ2⟩
  rcases h'' with ⟨hγ1, hγ2⟩

  have h1 : γ = π - α - β := by linarith

  have h2 : cos γ = - cos (α + β) := by
    rw [show γ = π - (α + β) by linarith]
    have : cos (π - (α + β)) = - cos (α + β) := by
      rw [cos_pi_sub]
    linarith

  have h3 : cos (α + β) = cos α * cos β - sin α * sin β := by
    rw [cos_add]

  have h4 : cos γ = - (cos α * cos β - sin α * sin β) := by
    rw [h2, h3]

  have h5 : cos α + cos β + cos γ = cos α + cos β - (cos α * cos β - sin α * sin β) := by
    rw [h4]
    all_goals ring

  rw [h5]

  have h6 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α

  have h7 : sin β ^ 2 + cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β

  have h8 : sin α > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith

  have h9 : sin β > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith

  nlinarith [sq_nonneg (cos α - cos β), sq_nonneg (cos α - 1), sq_nonneg (cos β - 1), 
          sq_nonneg (sin α - sin β), 
          Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
          mul_pos h8 h9, 
          sq_pos_of_pos h8, sq_pos_of_pos h9]