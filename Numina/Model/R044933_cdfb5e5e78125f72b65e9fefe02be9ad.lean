import Mathlib

open Real Set
open scoped Real

theorem inequalities_245734 (x y z : ℝ) (hx : 0 ≤ x ∧ x ≤ π/2) (hy : 0 ≤ y ∧ y ≤ π/2) (hz : 0 ≤ z ∧ z ≤ π/2) :
    cos x + cos y + cos z + cos (x + y + z) ≥ 0 := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  rcases hz with ⟨hz0, hz1⟩
  have h1 : cos x ≥ 0 := by apply cos_nonneg_of_mem_Icc; constructor <;> linarith [hx0, hx1, Real.pi_pos]
  have h2 : cos y ≥ 0 := by apply cos_nonneg_of_mem_Icc; constructor <;> linarith [hy0, hy1, Real.pi_pos]
  have h3 : cos z ≥ 0 := by apply cos_nonneg_of_mem_Icc; constructor <;> linarith [hz0, hz1, Real.pi_pos]
  have h6 : sin x ≥ 0 := by apply sin_nonneg_of_nonneg_of_le_pi; linarith [hx0, Real.pi_pos]; linarith [hx1, Real.pi_pos]
  have h7 : sin y ≥ 0 := by apply sin_nonneg_of_nonneg_of_le_pi; linarith [hy0, Real.pi_pos]; linarith [hy1, Real.pi_pos]
  have h8 : sin z ≥ 0 := by apply sin_nonneg_of_nonneg_of_le_pi; linarith [hz0, Real.pi_pos]; linarith [hz1, Real.pi_pos]
  have h5 : cos (x + y + z) = cos x * cos y * cos z - sin x * sin y * cos z - sin x * cos y * sin z - cos x * sin y * sin z := by
    rw [cos_add, cos_add]
    simp [sin_add, cos_add]
    <;> ring
  rw [h5]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z, 
          mul_nonneg (show 0 ≤ cos x by linarith) (show 0 ≤ cos y by linarith), 
          mul_nonneg (show 0 ≤ cos y by linarith) (show 0 ≤ cos z by linarith), 
          mul_nonneg (show 0 ≤ cos z by linarith) (show 0 ≤ cos x by linarith),
          sq_nonneg (cos x - cos y), sq_nonneg (cos y - cos z), sq_nonneg (cos z - cos x), 
          sq_nonneg (sin x - sin y), sq_nonneg (sin y - sin z), sq_nonneg (sin z - sin x)]