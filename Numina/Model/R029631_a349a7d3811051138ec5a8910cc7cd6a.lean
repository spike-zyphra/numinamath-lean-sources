import Mathlib

open Real Set
open scoped Real

theorem inequalities_316965 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) :
    (1 + 1 / sin α) * (1 + 1 / cos α) > 5 := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : 0 < sin α := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]

  have h2 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor
    all_goals
      linarith [hα1, hα2, Real.pi_pos]

  have h3 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α

  have h4 : sin α * cos α > 0 := mul_pos h1 h2

  have h5 : (1 + 1 / sin α) * (1 + 1 / cos α) - 5 > 0 := by
    have h5 : (1 + 1 / sin α) * (1 + 1 / cos α) - 5 =
        ((sin α + 1) * (cos α + 1) - 5 * (sin α * cos α)) / (sin α * cos α) := by
      field_simp [h1, h2]
      <;> ring_nf <;> field_simp [h1, h2]
      <;> ring
    rw [h5]
    apply div_pos
    nlinarith [sq_pos_of_pos h1, sq_pos_of_pos h2, sq_nonneg (sin α - cos α), sq_nonneg (sin α + cos α - 1), h3, Real.sin_sq_add_cos_sq α, mul_pos h1 h2]
    positivity

  linarith