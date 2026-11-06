import Mathlib

open Real Set
open scoped Real

theorem inequalities_252369 (α : Real) (hα : α ∈ Ioo 0 π) :
    sin α + (1/2)*sin (2*α) + (1/3)*sin (3*α) > 0 := by
  rcases hα with ⟨h1, h2⟩
  have h3 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    . linarith
    . linarith
  have h4 : sin (2 * α) = 2 * sin α * cos α := by
    rw [sin_two_mul]
  have h5 : sin (3 * α) = 3 * sin α - 4 * sin α ^ 3 := by
    rw [sin_three_mul]
  rw [h4, h5]
  have h6 : sin α + (1 / 2) * (2 * sin α * cos α) + (1 / 3) * (3 * sin α - 4 * sin α ^ 3) =
    sin α * (2 + cos α - (4 / 3) * sin α ^ 2) := by
    ring_nf
  rw [h6]
  have h7 : 2 + cos α - (4 / 3) * sin α ^ 2 > 0 := by
    have h8 : sin α ^ 2 = 1 - cos α ^ 2 := by
      have h9 : cos α ^ 2 + sin α ^ 2 = 1 := by
        exact cos_sq_add_sin_sq α
      nlinarith
    rw [h8]
    nlinarith [sq_nonneg (cos α - -1 / 4), sq_nonneg (cos α - -1 / 2), sq_nonneg (cos α - 1 / 2), sq_nonneg (cos α * 2 - 1), sq_nonneg (cos α * 2 + 1),
      sq_nonneg (cos α * 4 - 1), sq_nonneg (cos α * 4 + 1),
      Real.cos_sq_add_sin_sq α, Real.sin_sq_le_one α, Real.cos_le_one α, Real.neg_one_le_cos α]
  nlinarith