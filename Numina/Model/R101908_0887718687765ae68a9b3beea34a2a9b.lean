import Mathlib

open Real Set
open scoped Real

theorem algebra_11556 (α : Real) (hα : α ∈ Ioo 0 (π/2)) :
    sin α ^ 3 / cos α + cos α ^ 3 / sin α ≥ 1 := by
  rcases hα with ⟨h1, h2⟩
  have h3 : 0 < sin α := by apply sin_pos_of_pos_of_lt_pi; linarith; linarith
  have h4 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo 
    constructor <;> linarith [h1, h2, Real.pi_pos]
  have h5 : sin α ^ 4 + cos α ^ 4 ≥ sin α * cos α := by 
    nlinarith [sq_nonneg (sin α ^ 2 - cos α ^ 2), sq_nonneg (sin α * cos α - 1 / 2),
      Real.sin_sq_add_cos_sq α, mul_pos h3 h4, sq_nonneg (sin α ^ 2 - 1 / 2), sq_nonneg (cos α ^ 2 - 1 / 2), 
      mul_pos h3 h4
    ]
  have h5' : sin α ^ 3 / cos α + cos α ^ 3 / sin α - 1 ≥ 0 := by 
    have h7 : sin α ^ 3 / cos α + cos α ^ 3 / sin α - 1 = (sin α ^ 4 + cos α ^ 4 - sin α * cos α) / (sin α * cos α) := by 
      field_simp [show 0 < cos α by linarith, show 0 < sin α by linarith]
      <;> ring 
    rw [h7]
    have h8 : sin α ^ 4 + cos α ^ 4 ≥ sin α * cos α := by linarith
    have h9 : sin α ^ 4 + cos α ^ 4 - sin α * cos α ≥ 0 := by linarith
    have h10 : sin α * cos α > 0 := mul_pos h3 h4
    have h11 : (sin α ^ 4 + cos α ^ 4 - sin α * cos α) / (sin α * cos α) ≥ 0 := by 
      apply div_nonneg 
      linarith 
      linarith
    linarith
  linarith [h5']