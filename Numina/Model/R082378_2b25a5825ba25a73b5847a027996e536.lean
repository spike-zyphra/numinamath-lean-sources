import Mathlib

open Real Set
open scoped Real

theorem inequalities_285959 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) :
    3 ≤ sin (2 * α) + 2 / sin (2 * α) := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : 0 < 2 * α := by linarith
  have h2 : 2 * α < π := by linarith [Real.pi_pos]
  have h3 : 0 < sin (2 * α) := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith [Real.pi_pos]
  have h4 : sin (2 * α) + 2 / sin (2 * α) - 3 ≥ 0 := by
    have h5 : sin (2 * α) > 0 := h3
    have h6 : sin (2 * α) * (sin (2 * α) + 2 / sin (2 * α) - 3) ≥ 0 := by
      have h7 : sin (2 * α) * (sin (2 * α) + 2 / sin (2 * α) - 3) =
        (sin (2 * α)) ^ 2 + 2 - 3 * sin (2 * α) := by
        field_simp [h5]
        <;> ring
      rw [h7]
      nlinarith [sq_nonneg (sin (2 * α) - 1), sq_nonneg (sin (2 * α) - 2), 
        Real.sin_sq_le_one (2 * α), h5]
    nlinarith [h5]
  linarith [h4]