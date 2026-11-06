import Mathlib

open Real Set
open scoped Real

theorem inequalities_308803 (α : ℝ) :
  2 + sin α + cos α ≥ 2 / (2 - sin α - cos α) := by

  have h1 : 2 - sin α - cos α > 0 := by
    nlinarith [sq_nonneg (sin α + cos α - 1), sq_nonneg (sin α - cos α), Real.sin_sq_add_cos_sq α, sq_nonneg (sin α - 1), sq_nonneg (cos α - 1)]

  have h2 : 2 + sin α + cos α ≥ 2 / (2 - sin α - cos α) := by
    have h4 : (2 + sin α + cos α) - 2 / (2 - sin α - cos α) ≥ 0 := by
      have h3 : (2 + sin α + cos α) * (2 - sin α - cos α) - 2 ≥ 0 := by
        nlinarith [sq_nonneg (sin α - cos α), sq_nonneg (sin α + cos α - 1), sq_nonneg (sin α - 1), sq_nonneg (cos α - 1), Real.sin_sq_add_cos_sq α, mul_self_nonneg (sin α - cos α), mul_self_nonneg (sin α + cos α)]
      have h5 : (2 - sin α - cos α) > 0 := h1
      have h6 : ((2 + sin α + cos α) - 2 / (2 - sin α - cos α)) = ((2 + sin α + cos α) * (2 - sin α - cos α) - 2) / (2 - sin α - cos α) := by
        field_simp [show 2 - sin α - cos α ≠ 0 by linarith]
        <;> nlinarith
      rw [h6]
      apply div_nonneg
      linarith [h3]
      linarith
    linarith
  exact h2