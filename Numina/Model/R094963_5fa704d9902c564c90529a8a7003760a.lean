import Mathlib

open Real Set
open scoped Real

theorem algebra_153808 (α β : ℝ) :
  (cos α * cos β - cos (α + β)) / (cos (α - β) - sin α * sin β) =
  tan α * tan β := by
    have h_cos_add : cos (α + β) = cos α * cos β - sin α * sin β := by
      rw [cos_add]
    have h_cos_sub : cos (α - β) = cos α * cos β + sin α * sin β := by
      rw [cos_sub]

    have num_eq : cos α * cos β - cos (α + β) = sin α * sin β := by
      rw [h_cos_add]
      all_goals
        linarith

    have denom_eq : cos (α - β) - sin α * sin β = cos α * cos β := by
      rw [h_cos_sub]
      all_goals
        linarith

    rw [num_eq, denom_eq]

    have tan_eqsin_div_cos : tan α = sin α / cos α := by
      rw [tan_eq_sin_div_cos]
    have tan_eqsin_div_cos' : tan β = sin β / cos β := by
      rw [tan_eq_sin_div_cos]

    rw [tan_eqsin_div_cos, tan_eqsin_div_cos']
    <;> field_simp <;> ring
    <;> field_simp <;> linarith