import Mathlib

open Real Set
open scoped Real

theorem inequalities_292771 (α β : ℝ) (hα : α ∈ Ioo 0 (π/2)) (hβ : β ∈ Ioo 0 (π/2)) :
    9 ≤ 1 / cos α ^ 2 + 1 / (sin α ^ 2 * sin β ^ 2 * cos β ^ 2) := by
  rcases hα with ⟨hα1, hα2⟩
  rcases hβ with ⟨hβ1, hβ2⟩
  have h1 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]
  have h2 : 0 < sin α := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]
  have h3 : 0 < sin β := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [hβ1, hβ2, Real.pi_pos]
    linarith [hβ1, hβ2, Real.pi_pos]
  have h4 : 0 < cos β := by 
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hβ1, hβ2, Real.pi_pos]
    linarith [hβ1, hβ2, Real.pi_pos]
  have h5 : 0 < sin α ^ 2 * sin β ^ 2 * cos β ^ 2 := by positivity
  have h6 : 0 < cos α ^ 2 := by positivity

  have h7 : sin β ^ 2 * cos β ^ 2 ≤ 1 / 4 := by 
    nlinarith [sq_nonneg (sin β ^ 2 - cos β ^ 2), sq_nonneg (sin β * cos β - 1 / 2), Real.sin_sq_add_cos_sq β]

  have h8 : sin α ^ 2 * sin β ^ 2 * cos β ^ 2 ≤ sin α ^ 2 * (1 / 4) := by 
    nlinarith [h7, mul_pos h2 h3, mul_pos h2 h4]

  have h9 : 1 / (sin α ^ 2 * sin β ^ 2 * cos β ^ 2) ≥ 4 / sin α ^ 2 := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h8, mul_pos h2 h3, mul_pos h2 h4]

  have h12 : 1 / cos α ^ 2 + 4 / sin α ^ 2 ≥ 9 := by 
    have h13 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    have h14 : 0 < cos α ^ 2 := by positivity
    have h15 : 0 < sin α ^ 2 := by positivity
    have h16 : 1 / cos α ^ 2 + 4 / sin α ^ 2 - (9 : ℝ) ≥ 0 := by
      have h17 : (1 / cos α ^ 2 + 4 / sin α ^ 2 - (9 : ℝ)) = (sin α ^ 2 + 4 * cos α ^ 2 - 9 * (cos α ^ 2 * sin α ^ 2)) / (cos α ^ 2 * sin α ^ 2) := by 
        field_simp [h14, h15]
        <;> nlinarith [Real.sin_sq_add_cos_sq α]
      rw [h17]
      have h18 : sin α ^ 2 + 4 * cos α ^ 2 - 9 * (cos α ^ 2 * sin α ^ 2) ≥ 0 := by
        nlinarith [sq_nonneg (sin α ^ 2 - 2 / 3), sq_nonneg (cos α ^ 2 - 2 / 3), Real.sin_sq_add_cos_sq α, h13, mul_pos h14 h15]
      apply div_nonneg h18
      positivity
    linarith

  have h13 : 1 / cos α ^ 2 + 1 / (sin α ^ 2 * sin β ^ 2 * cos β ^ 2) ≥ 1 / cos α ^ 2 + 4 / sin α ^ 2 := by 
    linarith [h9]

  linarith [h12, h13]